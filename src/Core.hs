{-# LANGUAGE 
    PatternSynonyms, GADTs, ScopedTypeVariables, TupleSections, ViewPatterns, 
    FlexibleInstances, MultiParamTypeClasses, RecursiveDo, QuasiQuotes, 
    GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric, DeriveAnyClass, 
    DeriveFunctor, FlexibleContexts, RankNTypes, OverloadedStrings, RecordWildCards, 
    StandaloneDeriving, DeriveDataTypeable, TemplateHaskell #-}

module Core where

import qualified LamPi

import Data.List(intercalate, elemIndex)
import NeatInterpolation (text)


import Data.Text(Text)
import qualified Data.Text          as T
import           Text.Earley
import           Text.Earley.Mixfix(Associativity(..), Holey, mixfixExpression)

-- import           Text.Earley.Mixfix

-- import           Text.Regex         (mkRegex, splitRegex)
-- import Data.Tree
import Data.String(IsString(..))
import Data.String.Conv
import Data.List(groupBy)
-- import           Data.Singletons
import GHC.Generics(Generic)
import Data.Hashable(Hashable(..))
import Control.Monad.State
import Control.Monad.Except

import Data.Bifunctor(bimap)
import Control.Arrow(first,second)

-- import Data.HashSet(Set)
import qualified Data.HashSet as HS

import Data.Char(isDigit, isLower)

import Control.Applicative((<|>), many)

import Data.Maybe(fromJust)

import Data.Set(Set)
import qualified Data.Set as S

import Data.Map(Map)
import qualified Data.Map as M

import Data.List(sortBy)


import Language.Haskell.TH.Quote(QuasiQuoter(..), dataToExpQ)
import qualified Language.Haskell.TH.Syntax as THSyntax
import Data.Data(Data,Typeable, cast)

import Data.Has

infixl :$:


-- newtype Ctxt name = Ctxt { unCtxt :: Set (Exp name) } deriving (Eq, Show, Ord, Data, Typeable) 

data Arg n = Implicit n | Unnamed | Named n | Synthesized -- | ImplicitNamedArr n 
    deriving (Show, Eq, Ord, Data, Typeable, Functor)
-- data AppKind n = ExplicitApp | ImplicitNamedApp n deriving (Show, Eq, Functor, Generic)

data Exp name where
    V :: name -> Exp name
    Name :: name -> Exp name 
    IntE :: Int -> Exp name 
    (:$:) :: Exp name -> Exp name -> Exp name -- e e
    (:|$|:) :: Exp name -> Exp name -> Exp name -- e e
    Pi :: Arg name -> Exp name -> Exp name -> Exp name
    Set :: [Exp name] -> Exp name
    Hole :: Exp name
    InferMeta :: Exp name
    deriving (Show, Eq, Ord, Generic, Data, Typeable, Functor)

data Binding n = Bind n n | Unbound deriving (Show, Eq, Functor, Generic, Data, Typeable)


data TyCon name = TyCon name (Maybe name) (Exp name) (Binding name) -- Just (n,t) is: bind n in t 
    deriving (Show, Eq, Data, Typeable, Functor)


-- data PClause name = PClause name (Map name (Exp name)) [Exp name] (Exp name) deriving (Show, Eq, Data, Typeable)

-- pClauseMap :: Ord b => (a -> b) -> PClause a -> PClause b
-- pClauseMap f (PClause n ipats epats b) = 
--     PClause 
--         (f n) 
--         (M.foldrWithKey (\k v m -> M.insert (f k) (fmap f v) m) M.empty ipats)
--         (map (fmap f) epats) 
--         (fmap f b)

data Decl name = 
    Data LamPi.DataOpt name (Exp name) [TyCon name] 
  | Def name (Maybe (Exp name)) (Maybe name) (Exp name) -- [PClause name]
  | PropDef name (Exp name) (LamPi.SExpr name name)
  | OptDef (LamPi.SMTOpt name)
  | Lang name
  | TranslateDef name name [(Exp name, Maybe (Exp name), name)]
  | TranslateApp name name name
  deriving (Show, Eq, Data, Typeable)

instance Functor Decl where
    fmap f (Data opt n e tys) = Data opt (f n) (fmap f e) (map (fmap f) tys) 
    fmap f (Def n x y z) = Def (f n) (fmap (fmap f) x) (fmap f y) (fmap f z)
    fmap f (PropDef n exp sexp) = PropDef (f n) (fmap f exp) (bimap f f sexp)
    fmap f (OptDef o) = OptDef (fmap f o)
    fmap f (Lang l) = Lang (f l)
    fmap f (TranslateDef n l exps) = TranslateDef (f n) (f l) $ 
        map (\(a,b,c) -> (fmap f a, fmap (fmap f) b, f c)) exps
    fmap f (TranslateApp n l fn) = TranslateApp (f n) (f l) (f fn)

-- pattern ENArr x = ExplicitNamedArr x
-- pattern EArr    = ExplicitArr
-- pattern INArr x = ImplicitNamedArr x

-- pattern EApp   = ExplicitApp
-- pattern IApp x   = ImplicitNamedApp x

-- pattern (:$) :: Exp name -> Exp name -> Exp name
-- pattern a :$ b = App a ExplicitApp b


class PPrint a where
    pprint :: a -> String

instance PPrint name => PPrint (Exp name) where
    pprint (V name) = pprint name
    pprint (Name s) = "\'" ++ pprint s
    pprint (IntE i) = show i
    pprint (Set xs) = "⦃" ++ (intercalate "," (map pprint xs)) ++ "⦄"
    pprint (e :$: (e' :$: f'))     = pprint e ++ " (" ++ pprint (e' :$: f') ++ ")"
    pprint (e :$: f)              = pprint e ++ " " ++ pprint f
    pprint (e :|$|: f)              = pprint e ++ " {" ++ pprint f ++"}"
    pprint (Pi (Implicit n) e e') = "{" ++ pprint n ++ " : " ++ pprint e ++ "} -> " ++ pprint e' 
    pprint (Pi Synthesized e e') = "[" ++ pprint e ++ "] -> " ++ pprint e' 
    pprint (Pi Unnamed e e') = 
        (case e of 
            (Pi _ _ _) ->  "(" ++ pprint e ++ ")" 
            _ -> pprint e
        ) ++ " -> " ++ pprint e'
    pprint (Pi (Named n) e e') = "(" ++ pprint n ++ " : " ++ pprint e ++ ") -> " ++ pprint e'
    pprint Hole = "?"
    pprint InferMeta = "_"


-- instance PPrint name => PPrint [Arg name] where
--     pprint [] = ""
--     pprint [Unnamed c e] = pprint c ++ pprint e
--     pprint [Named c n e] = pprint c ++ "(" ++ pprint n ++ " : " ++ pprint e ++ ")"
--     pprint (Unnamed c e:xs) = pprint c ++ pprint e ++ " -> " ++ pprint xs
--     pprint (Named c n e:xs) = pprint c ++ "(" ++ pprint n ++ " : " ++ pprint e ++ ") -> " ++ pprint xs


instance PPrint name => PPrint (Binding name) where
    pprint (Bind n n') = " bind " ++ pprint n ++ " in " ++ pprint n'
    pprint Unbound = ""

instance PPrint name => PPrint (TyCon name) where
    pprint (TyCon n Nothing e b) = pprint n ++ " : " ++ pprint e ++ pprint b
    pprint (TyCon n (Just n') e b) = pprint n ++ " [" ++ pprint n' ++ "] : " ++ pprint e ++ pprint b

-- instance PPrint name => PPrint (PClause name) where
--     pprint (PClause name ipats epats b) = 
--         pprint name ++ " " ++ (intercalate " " $ ipatsPrint ++ epatsPrint) ++ " = " ++ pprint b
--         where
--             ipatsPrint =
--                 map (\(n,e) -> "{" ++ pprint n ++ " = " ++ pprint e ++ "}") $
--                     M.toList ipats
--             epatsPrint = map (\x -> case x of 
--                 (_ :$: _) -> "(" ++ pprint x ++ ")"
--                 _ -> pprint x) epats


instance (PPrint name, PPrint name2) => PPrint (LamPi.SExpr name name2) where
    pprint (LamPi.NAtom n) = "'" ++ pprint n
    pprint (LamPi.VAtom n) = pprint n
    pprint (LamPi.List xs) = "(" ++ (intercalate " " $ map pprint xs) ++ ")"

instance PPrint name => PPrint (Decl name) where
    pprint (Data opt n t tys) = "data " ++ pprint opt ++ pprint n ++ " : " ++ pprint t ++ " where\n" ++
        (intercalate " |\n" $ map ((" " ++) . pprint) tys) ++"\nend"
    pprint (Def n Nothing _ e) = "def " ++ pprint n ++ " = " ++ pprint e ++ "end"
    pprint (Def n (Just t) _ e) = 
        "def " ++ pprint n ++ " : " ++ pprint t ++ " where\n    " ++
                  pprint n ++ " = " ++ pprint t ++ "end"
    pprint (PropDef n t sexp) = 
        "prop " ++ pprint n ++ " : " ++ pprint t ++ " where\n    " ++
                  pprint sexp ++ "\nend"
    pprint (OptDef o) = pprint o
    pprint (Lang l) = "language " ++ pprint l
    pprint (TranslateDef n l defs) = "translation " ++ pprint n ++ " to "++ pprint l ++ " where\n" ++
        (intercalate " |\n" $ map (\(s, t, str) -> " " ++ pprint s ++ (case t of 
                Just t -> " : " ++ pprint t
                Nothing -> "") ++
            " -> " ++ "\"" ++ pprint str ++ "\"") defs) 
        ++ "\nend"
    pprint (TranslateApp n l out) = "translate " ++ pprint n ++ " to " ++ pprint l ++ " where\n output = " ++
        "\"" ++ pprint out ++ "\""
        ++ "\nend"

instance PPrint name => PPrint (LamPi.SMTOpt name) where
    pprint (LamPi.SMTCmd sexp) = "{-# SMT-command " ++ pprint sexp ++ " #-}"
    pprint (LamPi.SMTLogLevel i) = "{-# SMT-log-level " ++ show i ++ " #-}"
    pprint (LamPi.SMTLogEnabled b) = "{-# SMT-log-enabled " ++ show b ++ " #-}"


instance PPrint LamPi.DataOpt where
    pprint (LamPi.None) = "" 
    pprint (LamPi.LiftToSMT) = " [SMT] "
    -- pprint (Def n t patts) = "def " ++ pprint n ++ " : " ++ pprint t ++ " where\n" ++
    --     (intercalate " |\n" $ map ((" " ++) . pprint) patts) ++"\nend"


instance PPrint name => PPrint [Decl name] where
    pprint = (intercalate "\n\n") . (map pprint)

instance PPrint String where
    pprint = id

instance PPrint Text where
    pprint = toS


prefix :: String -> String -> Maybe String
prefix [] ys = Just ys
prefix (_:_) [] = Nothing
prefix (x:xs) (y:ys) | x == y = prefix xs ys
                     | otherwise = Nothing

newtype Row = Row Int 
    deriving newtype (Eq, Show, Num, Hashable) --, ToJSON, FromJSON, Hashable)

newtype Col = Col Int 
    deriving newtype (Eq, Show, Num, Hashable) --, ToJSON, FromJSON, Hashable)

data Token a = Token {
    unTok :: a,
    rowStart :: Row,
    rowEnd :: Row,
    colStart :: Col,
    colEnd :: Col
} deriving (Generic, Hashable)



tok :: a -> Token a
tok a = Token a (-1) (-1) (-1) (-1)


instance Show a => Show (Token a) where
    -- show = show . unTok
    show Token{..} 
        | rowStart == -1 || 
          rowEnd == -1   || 
          colStart == -1 ||
          colEnd == -1   = show unTok
        | otherwise = show unTok ++ " : Row (" ++ show rowStart ++ ":" ++ show rowEnd ++ "), Col (" ++ show colStart ++ ":" ++ show colEnd ++ ")"



-- instance ToJSON a => ToJSON (Token a)

instance Eq a => Eq (Token a) where
    t1 == t2 = unTok t1 == unTok t2

instance Ord a => Ord (Token a) where
    compare t1 t2 = compare (unTok t1) (unTok t2)

instance IsString a => IsString (Token a) where
    fromString s = Token (fromString s) 0 0 0 0

instance StringConv a b => StringConv (Token a) b where
    strConv l = strConv l . unTok


instance PPrint a => PPrint (Token a) where
    pprint = pprint . unTok



joinT :: Monoid a => Token a -> Token a -> Token a
joinT (Token t1 rS _ cS _) (Token t2 _ rE _ cE) = Token (t1 <> t2) rS rE cS cE



incrBy :: MonadState (Row, Col) m => Text -> m ()
incrBy t | T.null t = return ()
incrBy t | "\n" `T.isPrefixOf` t = do
    modify (bimap (+1) (const 1))
    incrBy $ T.tail t
incrBy t = do
    modify (second (+1))
    incrBy $ T.tail t

data DropOrKeepLabel = Drop | Keep | New deriving (Show, Eq)

data DropOrKeep a = DropOrKeep {
    label :: DropOrKeepLabel
  , content :: a
  } deriving (Show, Functor)

type TokenizerSettingsText = [(Text,Text -> ([DropOrKeep Text],Text))]

mkTokens :: MonadState (Row, Col) m => [DropOrKeep Text] -> m [DropOrKeep (Token Text)]
mkTokens [] = pure []
mkTokens (DropOrKeep l x:xs) = do
    (rowStart,colStart) <- get
    incrBy x
    (rowEnd,colEnd) <- get
    let token = Token x rowStart rowEnd colStart colEnd
    (DropOrKeep l token:) <$> mkTokens xs


startsWith :: TokenizerSettingsText -> Text -> Maybe ([DropOrKeep Text],Text)
startsWith [] str = Nothing
startsWith ((p,f):xs) str | p `T.isPrefixOf` str = Just $ f str
                              | otherwise = startsWith xs str


tokenizer :: MonadState (Row, Col) m => TokenizerSettingsText -> Text -> m [DropOrKeep (Token Text)]
tokenizer _  t | T.null t = return []
tokenizer ts (startsWith ts -> Just (potentialTokens, rest)) = do
    toks <- mkTokens potentialTokens
    (toks ++) <$> tokenizer ts rest
tokenizer ts t = do
    (rowStart,colStart) <- get
    incrBy $ T.singleton $ T.head t
    (rowEnd,colEnd) <- get
    let token = Token (T.singleton $ T.head t) rowStart rowEnd colStart colEnd
    tokens <- tokenizer ts $ T.tail t
    case tokens of
        [] -> return [DropOrKeep Keep token]
        (DropOrKeep Keep x:xs) -> return $ DropOrKeep Keep (joinT token x) : xs
        (x:xs) -> return $ DropOrKeep Keep token : x : xs


whitespace :: (Text, Text -> ([DropOrKeep Text],Text))
whitespace = (" ", f)
    where
        f :: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep Drop $ T.takeWhile (==' ') x], T.dropWhile (==' ') x)

newline :: (Text, Text -> ([DropOrKeep Text],Text))
newline = ("\n", f)
    where
        f :: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep Drop $ T.takeWhile (=='\n') x], T.dropWhile (=='\n') x)

tab :: (Text, Text -> ([DropOrKeep Text],Text))
tab = ("\t", f)
    where
        f :: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep Drop $ T.takeWhile (=='\t') x], T.dropWhile (=='\t') x)


reservedKeyword :: Text -> (Text, Text -> ([DropOrKeep Text],Text))
reservedKeyword w = (w, f)
    where
        f :: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep New w], fromJust $ T.stripPrefix w x)


block :: Text -> Text -> (Text, Text -> ([DropOrKeep Text],Text))
block start end = (start, f)
    where
        f:: Text -> ([DropOrKeep Text],Text)
        f x = 
            -- if we find the cloing block `end` then we add start and end as Tokens and take the string inbetween
            if end `T.isPrefixOf` rest' then
                ([DropOrKeep New start, DropOrKeep New quotePrefix, DropOrKeep New end], rest)
            -- if we can't find the closing `end` tag, we break on the first occurence of space/tab/newline
            else 
                ([DropOrKeep New quotePrefixAlt],restAlt)
            where
                (quotePrefix, rest') = T.breakOn end $ T.drop (T.length start) x
                rest = T.drop (T.length end) rest'

                quotePrefixAlt = T.takeWhile (\c -> not (c == ' ' || c == '\t' || c == '\n')) x
                restAlt = T.dropWhile (\c -> not (c == ' ' || c == '\t' || c == '\n')) x




blockLeft :: Text -> [Text] -> (Text, Text -> ([DropOrKeep Text],Text))
blockLeft start e = (start, \x -> (\(_,x,y) -> (x,y)) $ head $ sortBy (\(a,_,_) (b,_,_) -> compare a b) $ tryEnd e x)
    where

        tryEnd :: [Text] -> Text -> [(Int,[DropOrKeep Text],Text)]
        tryEnd [] x = []
        -- if we find the cloing block `end` then we add start as Token and take the string inbetween
        tryEnd (end:ends) x = 
            if end `T.isPrefixOf` rest then
                (T.length quotePrefix, [DropOrKeep New start, DropOrKeep New quotePrefix], rest) : tryEnd ends x
            else 
                tryEnd ends x
            where
                (quotePrefix, rest) = T.breakOn end $ T.drop (T.length start) x


blockDrop :: Text -> Text -> (Text, Text -> ([DropOrKeep Text],Text))
blockDrop start end = (start, f)
    where
        f:: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep Drop start, DropOrKeep Drop quotePrefix, DropOrKeep Drop end], rest)
            where
                (quotePrefix, rest') = T.breakOn end $ T.drop (T.length start) x
                rest = T.drop (T.length end) rest'




quoteEscape :: (Text, Text -> ([DropOrKeep Text],Text))
quoteEscape = ("\"", f)
    where
        f:: Text -> ([DropOrKeep Text],Text)
        f x = 
            -- if we find the cloing block `end` then we add start and end as Tokens and take the string inbetween
            if "\"" `T.isPrefixOf` rest then
                ([DropOrKeep New "\"", DropOrKeep New quotePrefix, DropOrKeep New "\""], T.drop 1 rest)
            -- if we can't find the closing `end` tag, we break on the first occurence of space/tab/newline
            else 
                ([DropOrKeep New quotePrefixAlt],restAlt)
            where
                quotePrefix = breakWithEscape $ T.drop 1 x
                rest = T.drop (T.length quotePrefix) $ T.drop 1 x

                quotePrefixAlt = T.takeWhile (\c -> not (c == ' ' || c == '\t' || c == '\n')) x
                restAlt = T.dropWhile (\c -> not (c == ' ' || c == '\t' || c == '\n')) x

                breakWithEscape :: Text -> Text
                breakWithEscape t 
                    | T.length t > 0 = 
                        let (pref,rest) = T.breakOn "\"" t in
                            case T.last pref of
                                '\\' -> T.concat [pref , "\"", breakWithEscape $ T.drop 1 rest]
                                _ -> pref
                    | otherwise = ""




quotes = block "\"" "\"" -- quoteEscape
quotes2 = block "\'\'\'" "\'\'\'" -- quoteEscape
name = blockLeft "\'"  [" ", "\n", "\t", "(", ")", "{", "}", "[", "]"] 



ignoreComment = blockDrop "--" "\n"
ignoreComment2 = blockDrop "{-" "-}"



intAux :: String -> (Text, Text -> ([DropOrKeep Text],Text))
intAux d = (T.pack d, \x -> ([DropOrKeep New $ T.takeWhile isDigit x], T.dropWhile isDigit x))


int :: [(Text, Text -> ([DropOrKeep Text],Text))]
int = map (intAux . show) [0..9]

-- quotes :: (Text, Text -> ([DropOrKeep Text],Text))
-- quotes = ("\"", f)
--     where
--         f x = ([DropOrKeep New "\"", DropOrKeep New quotePrefix, DropOrKeep New "\""], rest)
--             where
--                 quotePrefix = T.takeWhile (/= '\"') $ T.drop (T.length start) x
--                 rest = T.tail $ T.dropWhile (/= '\"') $ T.tail x

ignoreData = blockDrop "data" "end\n"
ignoreDef = blockDrop "def" "end\n"
ignoreProp = blockDrop "prop" "end"
ignoreInfixl = blockDrop "infixl" "\n"
ignoreInfixr = blockDrop "infixr" "\n"
ignoreInfix = blockDrop "infix" "\n"
ignoreLang = blockDrop "language" "\n"
ignoreTranslate = blockDrop "translate" "end\n"
ignoreTranslateDef = blockDrop "translation" "end\n"
ignoreSMT = blockDrop "smt" "end\n"


longestFirst :: Text -> Text -> Ordering
longestFirst a b = case compare (T.length a) (T.length b) of
    EQ -> compare a b
    LT -> GT
    GT -> LT

pretokenize :: (Row,Col) -> Text -> [Token Text]
pretokenize start_loc = 
    map content .
    filter ((/= Drop) . label) . 
    flip evalState start_loc . 
    tokenizer (
        whitespace : newline : tab : ignoreLang : ignoreTranslate : ignoreTranslateDef :
        ignoreSMT :
        ignoreData : ignoreDef : ignoreProp : ignoreComment : ignoreComment2 :
        (map reservedKeyword $ sortBy longestFirst reservedKeywords))


tokenize :: (Row,Col) -> [Infix] -> Text -> [Token Text]
tokenize start_loc is = 
    map content .
    filter ((/= Drop) . label) . 
    flip evalState start_loc . 
    tokenizer (-- int ++ (
        whitespace : newline : tab : 
        ignoreInfixl : ignoreInfixr : ignoreInfix : reservedKeyword "{-#" : reservedKeyword "#-}" : 
        quotes : quotes2 :
        ignoreComment : ignoreComment2 : ignoreSMT :
        name :
        map reservedKeyword reserved)
    --)
    where
        reserved = sortBy longestFirst $ reservedKeywords ++ map symb is



type G t = forall r. Grammar r (Prod r (Token Text) (Token Text) t)



parseG :: (Text -> [Token Text]) -> G t -> Text -> Either (Report (Token Text) [Token Text]) t
parseG tokenizer grammar t =
    case fullParses (parser $ grammar) $ tokenizer t of
        ([p] , _) -> Right p
        (_ , r) -> Left r

parseG' :: (Text -> [Token Text]) -> G t -> Text -> Either (Report Text [Text]) t
parseG' tokenizer grammar t =
    case fullParses (parser $ grammar) $ tokenizer t of
        ([p] , _) -> Right $ p
        (_ , (Report p e u)) -> Left $ Report p (map unTok e) (map unTok u)


parseG'' :: (Text -> [Token Text]) -> G t -> Text -> ([t], Report Text [Text])
parseG'' tokenizer grammar t =
    case fullParses (parser $ grammar) $ tokenizer t of
        (ps , Report p e u) -> (ps, Report p (map unTok e) (map unTok u))





-- rule for a variable name, excluding the set of reserved names
var :: HS.HashSet Text -> Prod r e (Token Text) (Token Text)
var reserved = satisfy (\t -> 
    let str = unTok t
        -- head_letter = T.head str 
    in
        not (str `HS.member` reserved) &&
        T.length str > 0)
         -- &&
        -- (isLower head_letter || head_letter == '_'))
        



data Infix = Infix {
    assoc :: Associativity
  , precedence :: Int
  , symb :: Text
} deriving (Show, Eq)


infixLang :: G [Infix]
infixLang = mdo
    name   <- rule $ unTok <$> var (HS.fromList reservedKeywords)
    number <- rule $ (read . T.unpack . unTok) <$> satisfy (\Token{..} -> T.all isDigit unTok)
    symbListR <- rule $
            pure []
        <|> (:[]) <$> name
        <|> (:) <$> name <*> (namedToken "," *> symbListR)
    expr <- rule $
            pure []
        <|> (\n xs ys -> (map (Infix NonAssoc n) xs) ++ ys) <$> (namedToken "infix" *> number) <*> symbListR <*> expr
        <|> (\n xs ys -> (map (Infix LeftAssoc n) xs) ++ ys) <$> (namedToken "infixl" *> number) <*> symbListR <*> expr
        <|> (\n xs ys -> (map (Infix RightAssoc n) xs) ++ ys) <$> (namedToken "infixr" *> number) <*> symbListR <*> expr
    return expr

reservedKeywords :: [Text]
reservedKeywords = 
    ["\"", "(", ")", "{|", "|}", "{", "}", "[", "]", "=>", "->", ":", ",", "\'", "?", "=", "_",  --, "true", "false", 
        -- "SMT-command", "SMT-log-level", "SMT-log-enabled", "language", "translate", "to", "bind",
        -- "end", "where", , "infix", "infixl", "infixr"
        "data", "def", "prop", "|"] 

bracketed :: (Eq b, IsString b) => Prod r b b a -> Prod r b b a
bracketed x = namedToken "(" *> x <* namedToken ")"

expLang :: [Infix] -> G (Exp (Token Text))
expLang infxLst = mdo
    varName <- rule $ var (HS.fromList $ reservedKeywords ++ map symb infxLst)
    varR <- rule $ 
            V <$> varName
        <|> V <$> (namedToken "(" *> satisfy (\s -> unTok s `HS.member` (HS.fromList $ map symb infxLst)) <* namedToken ")")

    nameR <- rule $ 
            Name <$> (namedToken "\'" *> satisfy (\s -> True))

    holeR <- rule $ (\_ -> Hole) <$> namedToken "?"
    inferMetaR <- rule $ (\_ -> InferMeta) <$> namedToken "_"

    listR <- rule $ 
            pure []
        <|> (:[]) <$> arrR
        <|> (:) <$> (arrR <* namedToken ",") <*> listR

    setR <- rule $ Set <$> (namedToken "{|" *> listR <* namedToken "|}")

    atom <- rule $ varR
        <|> nameR
        <|> namedToken "(" *> expr <* namedToken ")"
        <|> setR
        <|> holeR
        <|> inferMetaR
    appR <- rule $ 
            atom 
        <|> (:$:) <$> appR <*> atom -- (e .. e) (e) / A (e)
        <|> (:|$|:) <$> appR <*> (namedToken "{" *> atom <* namedToken "}")

    arrR <- rule $
            expr
        <|> Pi <$> (namedToken "{" *> (Implicit <$> varName) <* namedToken ":") <*> (arrR <* namedToken "}") <*> (namedToken "->" *> arrR)
        <|> Pi <$> (namedToken "(" *> (Named <$> varName) <* namedToken ":") <*> (arrR <* namedToken ")") <*> (namedToken "->" *> arrR)
        <|> (Pi Synthesized) <$> (namedToken "[" *> arrR <* namedToken "]") <*> (namedToken "->" *> arrR)
        <|> (Pi Unnamed) <$> expr <*> (namedToken "->" *> arrR)
        <|> (Pi Unnamed) <$> (namedToken "(" *> arrR <* namedToken ")") <*> (namedToken "->" *> arrR)
    
    expr <- mixfixExpression table appR appFun
    return arrR
    where
        appFun :: (Holey (Token Text) -> [Exp (Token Text)] -> Exp (Token Text))
        appFun [Nothing,Just t, Nothing] xs = foldl (:$:) (V t) xs

        table :: [[(Holey (Prod r (Token Text) (Token Text) (Token Text)), Associativity)]]
        table = map (map infixToHoley) sortedXs
            where
                xs :: [[Infix]]
                xs = groupBy (\a b -> (precedence a) == (precedence b)) infxLst
                
                sortedXs = sortBy (\a b -> compare (precedence (head a)) (precedence (head b))) xs

                infixToHoley :: Infix -> (Holey (Prod r (Token Text) (Token Text) (Token Text)), Associativity)
                infixToHoley Infix{..} = ([Nothing, Just $ namedToken $ tok symb, Nothing],assoc)


sExpLang :: [Infix] -> G (LamPi.SExpr (Token Text) (Token Text))
sExpLang infxLst = mdo
    varR <- rule $ LamPi.VAtom <$> var (HS.fromList $ reservedKeywords ++ map symb infxLst)

    nameR <- rule $ 
            LamPi.NAtom <$> (namedToken "\'" *> satisfy (\s -> True))

    listRAux <- rule $ (:[]) <$> varR
        <|> (:[]) <$> nameR
        <|> (:[]) <$> listR
        <|> (:) <$> atom <*> listRAux
        -- <|> (:) <$> nameR <*> listRAux
        -- <|> (:) <$> (namedToken "(" *> listR <* namedToken ")") <*> listRAux

    listR <- rule $ LamPi.List <$> (namedToken "(" *> listRAux <* namedToken ")")

    atom <- rule $ varR <|> nameR <|> listR
        
    return atom



expLangAppOnly :: [Infix] -> G (Exp (Token Text))
expLangAppOnly infxLst = mdo
    varR <- rule $ 
            V <$> var (HS.fromList $ reservedKeywords ++ map symb infxLst)
        <|> V <$> (namedToken "(" *> satisfy (\s -> unTok s `HS.member` (HS.fromList $ map symb infxLst)) <* namedToken ")")

    atom <- rule $ varR
        <|> namedToken "(" *> expr <* namedToken ")"
    appR <- rule $ 
            atom 
        <|> (:$:) <$> appR <*> atom -- (e .. e) (e) / A (e)
        <|> (:|$|:) <$> appR <*> (namedToken "{" *> atom <* namedToken "}")

    expr <- mixfixExpression table appR appFun
    return expr
    where
        appFun :: (Holey (Token Text) -> [Exp (Token Text)] -> Exp (Token Text))
        appFun [Nothing,Just t, Nothing] xs = foldl (:$:) (V t) xs

        table :: [[(Holey (Prod r (Token Text) (Token Text) (Token Text)), Associativity)]]
        table = map (map infixToHoley) sortedXs
            where
                xs :: [[Infix]]
                xs = groupBy (\a b -> (precedence a) == (precedence b)) infxLst
                
                sortedXs = sortBy (\a b -> compare (precedence (head a)) (precedence (head b))) xs

                infixToHoley :: Infix -> (Holey (Prod r (Token Text) (Token Text) (Token Text)), Associativity)
                infixToHoley Infix{..} = ([Nothing, Just $ namedToken $ tok symb, Nothing],assoc)

  
declLang :: [Infix] -> G [Decl (Token Text)]
declLang infxLst = mdo
    name  <- rule $ 
            var (HS.fromList $ reservedKeywords ++ map symb infxLst) 
        <|> namedToken "(" *> satisfy (\s -> unTok s `HS.member` (HS.fromList $ map symb infxLst)) <* namedToken ")"
    expR   <- expLang infxLst

    tyConName <- rule $
        ((\x -> TyCon x Nothing) <$> (name <* namedToken ":")) <|>
        (TyCon <$> name <*> (namedToken "[" *> (Just <$> name) <* namedToken "]" <* namedToken ":"))
    tyConR <- rule $ 
            pure []
        <|> (:[]) <$> (tyConName <*> expR <*> pure Unbound)
        <|> (:[]) <$> (tyConName <*> 
                expR <*> (namedToken "bind" *> (Bind <$> name <*> (namedToken "in" *> name))))

        <|> (:) <$> (tyConName <*> expR <*> pure Unbound) <*> (namedToken "|" *> tyConR)
        <|> (:) <$> (tyConName <*> 
                expR <*> (namedToken "bind" *> (Bind <$> name <*> (namedToken "in" *> name)))) <*> (namedToken "|" *> tyConR)

    dataR <- rule $ 
        ((Data LamPi.None) <$> (namedToken "data" *> name) <|>
         (Data LamPi.LiftToSMT) <$> (namedToken "data" *> namedToken "[" *> namedToken "SMT" *> namedToken "]" *> name))
        <*> 
        (namedToken ":" *> expR) <*> (namedToken "where" *> tyConR <* namedToken "end")

    defR <- rule $ 
            (\n e -> Def n Nothing Nothing e) <$> (namedToken "def" *> name <* namedToken "=") <*> 
                (expR <* namedToken "end")
        <|> Def <$> 
            (namedToken "def" *> name <* namedToken ":") <*> 
            ((Just <$> expR) <* namedToken "where") <*>
            ((Just <$> name) <* namedToken "=") <*>
            (expR <* namedToken "end")

    sExpR <- sExpLang infxLst

    propR <- rule $
        PropDef <$> (namedToken "prop" *> name <* namedToken ":") <*> 
            expR <*> (namedToken "where" *> sExpR <* namedToken "end")

    smtOpt <- rule $ OptDef . LamPi.SMTCmd <$> (namedToken "{-#" *> namedToken "SMT-command" *> sExpR <* namedToken "#-}")
    number <- rule $ (read . T.unpack . unTok) <$> satisfy (\Token{..} -> T.all isDigit unTok)
    smtLogLevel <- rule $ OptDef . LamPi.SMTLogLevel <$> (namedToken "{-#" *> namedToken "SMT-log-level" *> number <* namedToken "#-}")
    bool <- rule $ (namedToken "true" *> pure True) <|> (namedToken "false" *> pure False)
    smtLog <- rule $ OptDef . LamPi.SMTLogEnabled <$> 
        (namedToken "{-#" *> namedToken "SMT-log-enabled" *> bool <* namedToken "#-}") 

    langName <- rule $ satisfy (\s -> True)
    lang <- rule $ Lang <$> (namedToken "language" *> langName)

    translation <- rule $ TranslateDef <$> (namedToken "translation" *> name) <*> (namedToken "to" *> langName) <*>
        (namedToken "where" *> translateConsR <* namedToken "end")

    translate <- rule $ TranslateApp <$> (namedToken "translate" *> name) <*> (namedToken "to" *> langName) <*>
        (namedToken "where" *> namedToken "output" *> namedToken "=" *> stringR <* namedToken "end")

    expAppOnlyR   <- expLangAppOnly infxLst

    stringR <- rule $ 
        (namedToken "\"" *> satisfy (\s -> True) <* namedToken "\"") <|>
        (namedToken "\'\'\'" *> satisfy (\s -> True) <* namedToken "\'\'\'")

    translateConsR <- rule $ 
            pure []
        <|> (:[]) <$> 
            ((,,) <$> 
                (expAppOnlyR <* namedToken ":") <*> 
                ( Just <$> expAppOnlyR ) <*> 
                ( namedToken "->" *> stringR )
            )
        <|> (:[]) <$> 
            ( (,,) <$> expAppOnlyR <*> pure Nothing <*> (namedToken "->" *> stringR) )
        <|> (:) <$> 
            ((,,) <$> 
                (expAppOnlyR <* namedToken ":") <*> 
                ( Just <$> expAppOnlyR ) <*> 
                ( namedToken "->" *> stringR )
            ) <*> 
            (namedToken "|" *> translateConsR)
        <|> (:) <$> 
            ( (,,) <$> expAppOnlyR <*> pure Nothing <*> (namedToken "->" *> stringR) ) <*> 
            (namedToken "|" *> translateConsR)


    return $ many (dataR <|> defR <|> propR <|> smtOpt <|> smtLog <|> smtLogLevel <|> 
        lang <|> translation <|> translate)

newtype Constants = Constants { unConstants :: [Text] } deriving (Eq, Show)
newtype HoleCount = HoleCount { unHoleCount :: Int } deriving (Eq, Show)

getHoleCountAndIncrement :: (Has HoleCount s, MonadState s m) => m Int
getHoleCountAndIncrement = do
    (HoleCount c) <- getter <$> get
    modify (\s -> modifier (\(HoleCount c) -> HoleCount $ c+1) s)
    return c


mkTerm :: (MonadError String m, Has Constants s, Has HoleCount s, MonadState s m) => [Text] -> Exp (Token Text) -> m LamPi.Term
mkTerm _ Hole = do
    c <- getHoleCountAndIncrement
    return $ LamPi.Free $ LamPi.UserHole c
mkTerm _ InferMeta = do
    return $ LamPi.Free $ LamPi.InferMeta
mkTerm vars (V (Token "Set" _ _ _ _) :$: e') = do
    f' <- mkTerm vars e'
    return $ LamPi.SetT f'

-- mkTerm vars (Set xs) = return $ LamPi.MkSet _ (mkTerm vars xs) <- need a mechanism for hole here!!

mkTerm vars (e :$: e') = do
    f <- mkTerm vars e
    f' <- mkTerm vars e'
    return $ case f of
        (LamPi.:@:) x xs -> (LamPi.:@:) x (xs ++ [LamPi.E f'])
        _              -> (LamPi.:@:) f [LamPi.E f']
mkTerm vars (e :|$|: e') = do
    f <- mkTerm vars e
    f' <- mkTerm vars e'
    return $ case f of
        (LamPi.:@:) x xs -> (LamPi.:@:) x (xs ++ [LamPi.I f'])
        _              -> (LamPi.:@:) f [LamPi.I f']
mkTerm vars (Pi Unnamed e e') = (LamPi.Π Nothing) <$> mkTerm vars e <*> mkTerm ("":vars) e'
mkTerm vars (Pi Synthesized e e') = (LamPi.:⇒:) <$> mkTerm vars e <*> mkTerm vars e'
mkTerm vars (Pi (Named (Token n _ _ _ _)) e e') = (LamPi.Π (Just n)) <$> mkTerm vars e <*> mkTerm (n:vars) e'
mkTerm vars (Pi (Implicit (Token n _ _ _ _)) e e') = (LamPi.IΠ) <$> mkTerm vars e <*> mkTerm (n:vars) e'
mkTerm vars (Name (Token s _ _ _ _)) = return $ LamPi.MkName $ s
mkTerm vars (Set xs) = do
    xs' <- mapM (mkTerm vars) xs
    return $ LamPi.MkSet (LamPi.Free $ LamPi.InferMeta) $ S.toList $ S.fromList xs'

mkTerm vars (V (Token "*" _ _ _ _)) = return LamPi.StarT
mkTerm vars (V (Token "Type" _ _ _ _)) = return LamPi.StarT
mkTerm vars (V (Token "Prop" _ _ _ _)) = return LamPi.PropT
mkTerm vars (V (Token "Name" _ _ _ _)) = return $ LamPi.NameT
mkTerm vars (V (Token n _ _ _ _)) 
    | (Just i) <- elemIndex n vars = return $ LamPi.Bound i                           
    | otherwise = do
        (Constants constants) <- getter <$> get
        unless (n `elem` constants) $ throwError $ "Variable " ++ toS n ++ " not declared!"
        return $ LamPi.Free $ LamPi.Global n



getVars :: [Text] -> Exp (Token Text) -> [Text]
getVars vars (Pi Unnamed _ e') = getVars ("":vars) e'
getVars vars (Pi (Named (Token n _ _ _ _)) e e') = getVars (n:vars) e'
getVars vars (Pi (Implicit (Token n _ _ _ _)) e e') = getVars (n:vars) e'
getVars vars x = vars


-- mkTerm0 :: MonadError String m => LamPi.Γ -> Exp (Token Text) -> m LamPi.Term
-- mkTerm0 (LamPi.Γ g) e = flip evalStateT (Constants $ foldr (\(n,_) xs -> case n of 
--     LamPi.Global x -> x:xs 
--     _ -> xs) [] g, HoleCount 0) (mkTerm [] e)

makeDecl :: (MonadError String m, Has Constants s, Has HoleCount s, MonadState s m) => [Decl (Token Text)] -> m [LamPi.Decl]
makeDecl [] = return []
makeDecl (Data opt (Token n _ _ _ _) t cs:xs) = do
    t' <- mkTerm [] t
    modify (\s -> modifier (\(Constants xs) -> Constants $ n:xs) s)
    cs' <- mapM addCons cs
    -- g' <- LamPi.defineDecl0 g (LamPi.Data n t' cs')
    xs' <- makeDecl xs
    return $ LamPi.Data opt n t' cs':xs'

    where
        -- addCons :: TyCon (Token Text) -> (Text, LamPi.Term)
        addCons (TyCon (Token n _ _ _ _) n' e _) = do
            e' <- mkTerm [] e
            modify (\s -> modifier (\(Constants xs) -> Constants $ n:xs) s)
            return (n, fmap unTok n', e')
makeDecl (Def (Token n _ _ _ _) Nothing Nothing trm:xs) = do
    trm' <- mkTerm [] trm
    xs' <- makeDecl xs
    return $ LamPi.Def n Nothing trm':xs'
makeDecl (Def (Token n _ _ _ _) (Just ty) (Just (Token n' _ _ _ _)) trm:xs) | n == n' = do
    trm' <- mkTerm [] trm
    ty' <- mkTerm [] ty
    xs' <- makeDecl xs
    return $ LamPi.Def n (Just ty') trm':xs'
makeDecl (Def (Token n _ _ _ _) (Just ty) (Just (Token n' _ _ _ _)) trm:xs) | otherwise = error $ "name of function does not correspond to the definition"
makeDecl (PropDef (Token n _ _ _ _) t sexp:xs) = do
    t' <- mkTerm [] t
    let vars = reverse $ getVars [] t
    modify (\s -> modifier (\(Constants xs) -> Constants $ n:xs) s)
    xs' <- makeDecl xs
    sexp' <- setVars vars (bimap unTok unTok sexp)
    return $ LamPi.PropDef n t' sexp':xs'

    where
        setVars vars (LamPi.NAtom n) = return $ LamPi.NAtom n
        setVars vars (LamPi.VAtom n)
            | (Just i) <- elemIndex n vars = return $ LamPi.VAtom i                           
            | otherwise = return $ LamPi.NAtom n
        setVars vars (LamPi.List xs) = do
            xs' <- mapM (setVars vars) xs
            return $ LamPi.List xs'
makeDecl (OptDef o:xs) = do
    xs' <- makeDecl xs
    return $ LamPi.SMTOptDef (fmap unTok o):xs'
makeDecl (Lang l:xs) = do
    xs' <- makeDecl xs
    return $ LamPi.Lang (unTok l):xs'
makeDecl (TranslateDef tyN l defs:xs) = do
    xs' <- makeDecl xs
    let defs' = map (\(c,t,s) -> (mkTermTranslate c, fmap mkTermTranslate t, unTok s)) defs
    return $ LamPi.TranslateDef (unTok tyN) (unTok l) defs':xs'
makeDecl (TranslateApp n l fn:xs) = do
    xs' <- makeDecl xs
    return $ LamPi.TranslateApp (unTok n) (unTok l) (unTok fn):xs'


mkTermTranslate :: Exp (Token Text) -> LamPi.Term
mkTermTranslate (V (Token "Set" _ _ _ _) :$: e) = LamPi.SetT $ mkTermTranslate e
mkTermTranslate (e :$: e') = do
    let f = mkTermTranslate e
    let f' = mkTermTranslate e'
    case f of
        (LamPi.:@:) x xs -> (LamPi.:@:) x (xs ++ [LamPi.E f'])
        _                -> (LamPi.:@:) f [LamPi.E f']
mkTermTranslate (e :|$|: e') = do
    let f = mkTermTranslate e
    let f' = mkTermTranslate e'
    case f of
        (LamPi.:@:) x xs -> (LamPi.:@:) x (xs ++ [LamPi.I f'])
        _                -> (LamPi.:@:) f [LamPi.I f']
mkTermTranslate (Set xs) = do
    let xs' = map mkTermTranslate xs
    LamPi.MkSet (LamPi.Free $ LamPi.InferMeta) $ S.toList $ S.fromList xs'
mkTermTranslate (V (Token "*" _ _ _ _)) = LamPi.StarT
mkTermTranslate (V (Token "Type" _ _ _ _)) = LamPi.StarT
mkTermTranslate (V (Token "Prop" _ _ _ _)) = LamPi.PropT
mkTermTranslate (V (Token "Name" _ _ _ _)) = LamPi.NameT
mkTermTranslate (V (Token n _ _ _ _)) = LamPi.Free $ LamPi.Global n


runSTE :: StateT (HoleCount, Constants) (Except String) v -> Either String v
runSTE m = runExcept (flip evalStateT (HoleCount 0, Constants []) m)

t3raw :: QuasiQuoter
t3raw = QuasiQuoter {
    quoteExp  = compileRaw
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the t3 quasiquoter."
 
compileRaw :: String -> THSyntax.Q THSyntax.Exp
compileRaw s = do
    THSyntax.Loc{..} <- THSyntax.location

    let start_loc = bimap Row Col loc_start
    case parseG (pretokenize start_loc) infixLang $ toS s of
        Right is -> do
            let tokens = tokenize start_loc is $ toS s

            -- putStrLn "Infix loaded:"
            -- putStrLn $ show is
            -- putStrLn "\nTokenized output:"
            -- fail $ show $ map unTok $ (tokenize start_loc is) $ toS s
            case parseG'' (tokenize start_loc is) (declLang is) $ toS s of
                ([], Report{..}) -> fail $ mkError $ tokens !! position
                ([x],_) -> dataToExpQ (const Nothing) $ map (fmap ((toS :: Text -> String) . unTok)) x
                    -- putStrLn "\nParsed and pretty printed output:\n"
                    -- putStrLn $ pprint $ map (declMap unTok) x
                (xs,_) -> fail $ "Ambiguous parse:\n" ++ (intercalate "\n" $ map pprint (xs :: [[Decl (Token Text)]]))
        Left e -> fail $ "Infix preprocessing failed:\n" ++ show e

    where 
        mkError :: Token Text -> String
        mkError (Token{..}) = 
            "Parsing error at " ++ toS unTok ++ 
            " (line " ++ show rowStart ++ ", column " ++ show colStart ++ ")"
    



t3 :: QuasiQuoter
t3 = QuasiQuoter {
    quoteExp  = compileTerm
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the t3 quasiquoter."
 


liftText :: Text -> THSyntax.Q THSyntax.Exp
liftText txt = THSyntax.AppE (THSyntax.VarE 'T.pack) <$> THSyntax.lift (T.unpack txt)

-- myThHelper :: FilePath -> THSyntax.Q THSyntax.Exp
-- myThHelper path =
--   runIO (compileThatFile path) >>= liftText

liftDataWithText :: Data a => a -> THSyntax.Q THSyntax.Exp
liftDataWithText = dataToExpQ (\a -> liftText <$> cast a)


compileTerm :: String -> THSyntax.Q THSyntax.Exp
compileTerm s = do
    THSyntax.Loc{..} <- THSyntax.location

    let start_loc = bimap Row Col loc_start
    case parseG (pretokenize start_loc) infixLang $ toS s of
        Right is -> do
            let tokens = tokenize start_loc is $ toS s

            -- putStrLn "Infix loaded:"
            -- putStrLn $ show is
            -- putStrLn "\nTokenized output:"
            -- putStrLn $ show $ map unTok $ tokenize is $ toS s
            -- fail $ show $ map unTok $ (tokenize start_loc is) $ toS s
            case parseG'' (tokenize start_loc is) (declLang is) $ toS s of
                ([], Report{..}) -> fail $ mkError $ tokens !! position
                ([x],_) -> case runSTE $ makeDecl x of
                    Left e -> fail $ "converting to LambPi failed with error:\n" ++ e
                    Right d -> liftDataWithText d
                    -- putStrLn "\nParsed and pretty printed output:\n"
                    -- putStrLn $ pprint $ map (declMap unTok) x
                (xs,_) -> fail $ "Ambiguous parse:\n" ++ (intercalate "\n" $ map pprint (xs :: [[Decl (Token Text)]]))
        Left e -> fail $ "Infix preprocessing failed:\n" ++ show e

    where 
        mkError :: Token Text -> String
        mkError (Token{..}) = 
            "Parsing error at " ++ toS unTok ++ 
            " (line " ++ show rowStart ++ ", column " ++ show colStart ++ ")"
    



