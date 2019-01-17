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


infixl :$:


newtype Ctxt name = Ctxt { unCtxt :: Set (Exp name) } deriving (Eq, Show, Ord, Data, Typeable) 

data Arg n = Implicit (Ctxt n) n | Unnamed (Ctxt n) | Named (Ctxt n) n -- | ImplicitNamedArr n 
    deriving (Show, Eq, Ord, Data, Typeable)
-- data AppKind n = ExplicitApp | ImplicitNamedApp n deriving (Show, Eq, Functor, Generic)

argMap :: Ord b => (a -> b) -> Arg a -> Arg b
argMap f (Implicit (Ctxt c) e) = Implicit (Ctxt $ S.map (expMap f) c) (f e)

argMap f (Unnamed (Ctxt c)) = Unnamed (Ctxt $ S.map (expMap f) c)
argMap f (Named (Ctxt c) e) = Named (Ctxt $ S.map (expMap f) c) (f e)

data Exp name where
    V :: name -> Exp name
    String :: name -> Exp name 
    (:$:) :: Exp name -> Exp name -> Exp name -- e e
    (:|$|:) :: Exp name -> Exp name -> Exp name -- e e
    Pi :: Arg name -> Exp name -> Exp name -> Exp name
    deriving (Show, Eq, Ord, Generic, Data, Typeable)


expMap :: Ord b => (a -> b) -> Exp a -> Exp b
expMap f (V x) =  V $ f x
expMap f (String x) =  String $ f x
expMap f (e :$: e') =  expMap f e :$: expMap f e'
expMap f (e :|$|: e') =  expMap f e :|$|: expMap f e'
expMap f (Pi n e e') =  Pi (argMap f n) (expMap f e) (expMap f e')


data Binding n = Bind n n | Unbound deriving (Show, Eq, Functor, Generic, Data, Typeable)


data TyCon name = TyCon name (Exp name) (Binding name) -- Just (n,t) is: bind n in t 
    deriving (Show, Eq, Data, Typeable)


tyConMap :: Ord b => (a -> b) -> TyCon a -> TyCon b
tyConMap f (TyCon n ty b) = TyCon (f n) (expMap f ty) (fmap f b)


-- data PClause name = PClause name (Map name (Exp name)) [Exp name] (Exp name) deriving (Show, Eq, Data, Typeable)

-- pClauseMap :: Ord b => (a -> b) -> PClause a -> PClause b
-- pClauseMap f (PClause n ipats epats b) = 
--     PClause 
--         (f n) 
--         (M.foldrWithKey (\k v m -> M.insert (f k) (fmap f v) m) M.empty ipats)
--         (map (fmap f) epats) 
--         (fmap f b)


data Decl name = 
    Data name (Exp name) [TyCon name] 
  -- | Def name (Exp name) [PClause name]

  deriving (Show, Eq, Data, Typeable)


declMap :: Ord b => (a -> b) -> Decl a -> Decl b
declMap f (Data n args tycons) = Data (f n) (expMap f args) (map (tyConMap f) tycons)
-- declMap f (Def n args plcauses) = Def (f n) (map (argMap f) args) (map (pClauseMap f) plcauses) 

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
    pprint (String s) = "\"" ++ pprint s ++ "\""
    pprint (e :$: (e' :$: f'))     = pprint e ++ " (" ++ pprint (e' :$: f') ++ ")"
    pprint (e :$: f)              = pprint e ++ " " ++ pprint f
    pprint (e :|$|: f)              = pprint e ++ " {" ++ pprint f ++"}"
    pprint (Pi (Implicit ctxt n) e e') = pprint ctxt ++ "{" ++ pprint n ++ " : " ++ pprint e ++ "} -> " ++ pprint e' 
    pprint (Pi (Unnamed ctxt) e e') = pprint ctxt ++ 
        (case e of 
            (Pi _ _ _) ->  "(" ++ pprint e ++ ")" 
            _ -> pprint e
        ) ++ " -> " ++ pprint e'
    pprint (Pi (Named ctxt n) e e') = pprint ctxt ++ "(" ++ pprint n ++ " : " ++ pprint e ++ ") -> " ++ pprint e'
        

instance PPrint name => PPrint (Ctxt name) where
    pprint (Ctxt c) | S.null c = ""
                    | otherwise = "{" ++ (intercalate "," $ map pprint $ S.toList c) ++ "} => " 

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
    pprint (TyCon n e b) = pprint n ++ " : " ++ pprint e ++ pprint b

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


instance PPrint name => PPrint (Decl name) where
    pprint (Data n t tys) = "data " ++ pprint n ++ " : " ++ pprint t ++ " where\n" ++
        (intercalate " |\n" $ map ((" " ++) . pprint) tys) ++"\nend"
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


blockDrop :: Text -> Text -> (Text, Text -> ([DropOrKeep Text],Text))
blockDrop start end = (start, f)
    where
        f:: Text -> ([DropOrKeep Text],Text)
        f x = ([DropOrKeep Drop start, DropOrKeep Drop quotePrefix, DropOrKeep Drop end], rest)
            where
                (quotePrefix, rest') = T.breakOn end $ T.drop (T.length start) x
                rest = T.drop (T.length end) rest'

quotes = block "\"" "\""



ignoreComment = blockDrop "--" "\n"

-- quotes :: (Text, Text -> ([DropOrKeep Text],Text))
-- quotes = ("\"", f)
--     where
--         f x = ([DropOrKeep New "\"", DropOrKeep New quotePrefix, DropOrKeep New "\""], rest)
--             where
--                 quotePrefix = T.takeWhile (/= '\"') $ T.drop (T.length start) x
--                 rest = T.tail $ T.dropWhile (/= '\"') $ T.tail x

ignoreData = blockDrop "data" "end"
ignoreDef = blockDrop "def" "end"
ignoreInfixl = blockDrop "infixl" "\n"
ignoreInfixr = blockDrop "infixr" "\n"
ignoreInfix = blockDrop "infix" "\n"


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
        whitespace : newline : tab : 
        ignoreData : ignoreDef : ignoreComment :
        (map reservedKeyword $ sortBy longestFirst reservedKeywords))


tokenize :: (Row,Col) -> [Infix] -> Text -> [Token Text]
tokenize start_loc is = 
    map content .
    filter ((/= Drop) . label) . 
    flip evalState start_loc . 
    tokenizer (
        whitespace : newline : tab : 
        ignoreInfixl : ignoreInfixr : ignoreInfix : ignoreComment : quotes :
        (map reservedKeyword $ sortBy longestFirst $ reservedKeywords ++ map symb is))



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
var :: HS.Set Text -> Prod r e (Token Text) (Token Text)
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
reservedKeywords = ["\"", "(", ")", "{", "}", "[", "]", "=>", "->", ":", ",", "data", "def", "end", "where", "bind", "|", "infix", "infixl", "infixr"] 

bracketed :: (Eq b, IsString b) => Prod r b b a -> Prod r b b a
bracketed x = namedToken "(" *> x <* namedToken ")"

expLang :: [Infix] -> G (Exp (Token Text))
expLang infxLst = mdo
    name <- rule $ var (HS.fromList $ reservedKeywords ++ map symb infxLst)
    varR <- rule $ 
            V <$> name
        <|> V <$> (namedToken "(" *> satisfy (\s -> unTok s `HS.member` (HS.fromList $ map symb infxLst)) <* namedToken ")")

    stringR <- rule $ 
            String <$> (namedToken "\"" *> satisfy (\s -> True) <* namedToken "\"")


    atom <- rule $ varR
        <|> stringR
        <|> namedToken "(" *> expr <* namedToken ")"
    appR <- rule $ 
            atom 
        <|> (:$:) <$> appR <*> atom -- (e .. e) (e) / A (e)
        <|> (:|$|:) <$> appR <*> (namedToken "{" *> atom <* namedToken "}")

    arrR <- rule $
            appR
        <|> Pi <$> (namedToken "{" *> (Implicit (Ctxt S.empty) <$> name) <* namedToken ":") <*> (expr <* namedToken "}") <*> (namedToken "->" *> expr)
        <|> Pi <$> (namedToken "(" *> (Named (Ctxt S.empty) <$> name) <* namedToken ":") <*> (expr <* namedToken ")") <*> (namedToken "->" *> expr)
        -- <|> (Pi (Unnamed (Ctxt S.empty))) <$> (namedToken "(" *> expr <* namedToken ")") <*> (namedToken "->" *> expr)
        <|> (Pi (Unnamed (Ctxt S.empty))) <$> appR <*> (namedToken "->" *> expr)
         
    expr <- mixfixExpression table arrR appFun
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
    tyConR <- rule $ 
            pure []
        <|> (:[]) <$> (TyCon <$> (name <* namedToken ":") <*> expR <*> pure Unbound)
        <|> (:[]) <$> (TyCon <$> (name <* namedToken ":") <*> 
                expR <*> (namedToken "bind" *> (Bind <$> name <*> (namedToken "in" *> name))))

        <|> (:) <$> (TyCon <$> (name <* namedToken ":") <*> expR <*> pure Unbound) <*> (namedToken "|" *> tyConR)
        <|> (:) <$> (TyCon <$> (name <* namedToken ":") <*> 
                expR <*> (namedToken "bind" *> (Bind <$> name <*> (namedToken "in" *> name)))) <*> (namedToken "|" *> tyConR)

    dataR <- rule $ 
        Data <$> (namedToken "data" *> name <* namedToken ":") <*> 
            expR <*> (namedToken "where" *> tyConR <* namedToken "end")
    -- declR

    -- clauseExpR <- rule $ ((V <$> var (HS.fromList reservedKeywords)) <|> bracketed expR)

    -- pattR <- rule $ 
    --         pure (M.empty, [])
    --     <|> (bimap id) <$> ((:) <$> clauseExpR) <*> pattR -- ... v ... / ... (e) ...
    --     <|> (flip bimap id) <$> ((M.insert) <$> (namedToken "{" *> name <* namedToken "=") <*> (expR <* namedToken "}")) <*> pattR -- ... { n = e } ...

    -- pClauseR <- rule $ (\n (ipats,epats) e -> PClause n ipats epats e) <$>
    --     name <*> pattR <*> (namedToken "=" *> expR)

    -- pClauseListR <- rule $
    --         (:[]) <$> pClauseR
    --     <|> (:) <$> pClauseR <*> (namedToken "|" *> pClauseListR)

    -- defR <- rule $ 
    --     Def <$> (namedToken "def" *> name <* namedToken ":") <*> 
    --         argsR <*> (namedToken "where" *> pClauseListR <* namedToken "end")


    return $ many dataR -- <|> defR)

type Constants = [Text]

mkTerm :: (MonadError String m, MonadState Constants m) => [Text] -> Exp (Token Text) -> m LamPi.Term
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
mkTerm vars (Pi (Unnamed _) e e') = (LamPi.Π) <$> mkTerm vars e <*> mkTerm ("":vars) e'
mkTerm vars (Pi (Named _ (Token n _ _ _ _)) e e') = (LamPi.Π) <$> mkTerm vars e <*> mkTerm (n:vars) e'
mkTerm vars (Pi (Implicit _ (Token n _ _ _ _)) e e') = (LamPi.IΠ) <$> mkTerm vars e <*> mkTerm (n:vars) e'
mkTerm vars (String (Token s _ _ _ _)) = return $ LamPi.MkString $ s
mkTerm vars (V (Token "*" _ _ _ _)) = return LamPi.Star
mkTerm vars (V (Token "Type" _ _ _ _)) = return LamPi.Star
mkTerm vars (V (Token "String" _ _ _ _)) = return $ LamPi.String
mkTerm vars (V (Token n _ _ _ _)) 
    | (Just i) <- elemIndex n vars = return $ LamPi.Bound i                           
    | otherwise = do
        constants <- get
        unless (n `elem` constants) $ throwError $ "Variable " ++ toS n ++ " not declared!"
        return $ LamPi.Free $ LamPi.Global n

mkTerm0 :: MonadError String m => LamPi.Γ -> Exp (Token Text) -> m LamPi.Term
mkTerm0 g e = flip evalStateT (foldr (\(n,_) xs -> case n of 
    LamPi.Global x -> x:xs 
    _ -> xs) [] g) (mkTerm [] e)

makeDecl :: (MonadError String m, MonadState Constants m) => [Decl (Token Text)] -> m [LamPi.Decl]
makeDecl [] = return []
makeDecl (Data (Token n _ _ _ _) t cs:xs) = do
    t' <- mkTerm [] t
    modify (n:)
    cs' <- mapM addCons cs
    -- g' <- LamPi.defineDecl0 g (LamPi.Data n t' cs')
    xs' <- makeDecl xs
    return $ LamPi.Data n t' cs':xs'

    where
        -- addCons :: TyCon (Token Text) -> (Text, LamPi.Term)
        addCons (TyCon (Token n _ _ _ _) e _) = do
            e' <- mkTerm [] e
            modify (n:)
            return (n, e')


runSTE :: StateT Constants (Except String) v -> Either String v
runSTE m = runExcept (flip evalStateT [] m)

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
            -- putStrLn $ show $ map unTok $ tokenize is $ toS s
            case parseG'' (tokenize start_loc is) (declLang is) $ toS s of
                ([], Report{..}) -> fail $ mkError $ tokens !! position
                ([x],_) -> dataToExpQ (const Nothing) $ map (declMap ((toS :: Text -> String) . unTok)) x
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
    



