{-# LANGUAGE 
    PatternSynonyms, GADTs, ScopedTypeVariables, TupleSections, ViewPatterns, 
    FlexibleInstances, MultiParamTypeClasses, RecursiveDo, QuasiQuotes, 
    GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric, DeriveAnyClass, 
    DeriveFunctor, FlexibleContexts, RankNTypes, OverloadedStrings, RecordWildCards #-}

module Core where
import Data.List(intercalate)
import NeatInterpolation (text)


import Data.Text(Text)
import qualified Data.Text          as T
import           Text.Earley
import           Text.Earley.Mixfix(Associativity(..), Holey)

-- import           Text.Earley.Mixfix

-- import           Text.Regex         (mkRegex, splitRegex)
-- import Data.Tree
import Data.String(IsString(..))
import Data.String.Conv
import Data.List(stripPrefix)
-- import           Data.Singletons
import GHC.Generics
import Data.Hashable(Hashable(..))
import Control.Monad.State

import Data.Bifunctor(bimap)
import Control.Arrow(first,second)

import Data.HashSet(Set)
import qualified Data.HashSet as S

import Data.Char(isDigit)

import Control.Applicative((<|>))

infixl :$

-- infix 9 :@, :@@

-- infixr 8 :->

type Name = String

data ArrKind n = ExplicitArr | ExplicitNamedArr n | ImplicitNamedArr n deriving (Show, Eq, Functor, Generic)
data AppKind n = ExplicitApp | ImplicitNamedApp n deriving (Show, Eq, Functor, Generic)

data Binding n = Bind n n | Unbound deriving (Show, Eq, Functor, Generic)

data Exp name where
    C :: name -> Exp name
    V :: name -> Exp name
    App :: Exp name -> AppKind name -> Exp name -> Exp name -- e e / e {x = e}
    Arr :: ArrKind name -> Exp name -> Exp name -> Exp name -- e -> e / (x : e) -> e / {x : e} -> e
    Refine :: name -> Exp name -> Exp name -> Exp name -- {@ x : e | e @}

    deriving (Show, Eq, Functor, Generic)


data TyCon name = TyCon name (Exp name) (Binding name) -- Just (n,t) is: bind n in t 
    deriving (Show, Eq, Functor)

data Trm name = 
    Data name (Exp name) [TyCon name] 
  | Decl name (Exp name) (Exp name)

  deriving (Show, Eq, Functor)


pattern ENArr x = ExplicitNamedArr x
pattern EArr    = ExplicitArr
pattern INArr x = ImplicitNamedArr x

pattern EApp   = ExplicitApp
pattern IApp x   = ImplicitNamedApp x

pattern (:$) :: Exp name -> Exp name -> Exp name
pattern a :$ b = App a ExplicitApp b


class PPrint a where
    pprint :: a -> String

instance PPrint name => PPrint (Exp name) where
    pprint (C name) = "C_" ++ pprint name

    pprint (V name) = pprint name
    

    pprint (App (Arr n' x' y') (IApp n) f) = "(" ++ pprint (Arr n' x' y') ++ ") { " ++ pprint n ++ " = " ++ pprint f ++ " }"
    pprint (App e (IApp n) f)              = pprint e ++ " { " ++ pprint n ++ " = " ++ pprint f ++ " }"

    pprint (App (Arr n' x' y') EApp (App e' n f')) = "(" ++ pprint (Arr n' x' y') ++ ") (" ++ pprint (App e' n f') ++ ")"
    pprint (App (Arr n' x' y') EApp (Arr n x y))   = "(" ++ pprint (Arr n' x' y') ++ ") (" ++ pprint (Arr n x y) ++ ")"
    pprint (App (Arr n' x' y') EApp e)             = "(" ++ pprint (Arr n' x' y') ++ ") " ++ pprint e

    pprint (App e EApp (App e' n' f')) = pprint e ++ " (" ++ pprint (App e' n' f') ++ ")"
    pprint (App e EApp (Arr n x y))    = pprint e ++ " (" ++ pprint (Arr n x y) ++ ")"
    pprint (App e EApp f)              = pprint e ++ " " ++ pprint f

    pprint (Arr (ENArr n) x y)         = "(" ++ pprint n ++ " : " ++ pprint x ++ ") -> " ++ pprint y
    pprint (Arr (INArr n) x y)         = "{" ++ pprint n ++ " : " ++ pprint x ++ "} -> " ++ pprint y
    pprint (Arr EArr (Arr n' x' y') y) = "(" ++ pprint (Arr n' x' y') ++ ") -> " ++ pprint y
    pprint (Arr EArr x y)              = pprint x ++ " -> " ++ pprint y

    pprint (Refine name typ b) = "{@ " ++ pprint name ++ " : " ++ pprint typ ++ " | " ++ pprint b ++ " @}"


instance PPrint name => PPrint (Binding name) where
    pprint (Bind n n') = " bind " ++ pprint n ++ " in " ++ pprint n'
    pprint Unbound = ""

instance PPrint name => PPrint (TyCon name) where
    pprint (TyCon n e b) = pprint n ++ " : " ++ pprint e ++ pprint b

instance PPrint name => PPrint (Trm name) where
    pprint (Data n t tys) = "data " ++ pprint n ++ " : " ++ pprint t ++ " where\n" ++
        (intercalate " |\n" $ map ((" " ++) . pprint) tys)




instance PPrint Name where
    pprint = id

instance PPrint Text where
    pprint = toS


-- typeTypeDefn :: Type Name
-- typeTypeDefn = [] :-> C "Type"

-- nameTypeDefn :: Type Name
-- nameTypeDefn = [] :-> C "Name"



-- defnList :: Trm Name
-- defnList = 
--     Data "List" (["a" :@ C "Type"] :-> C "Type") [
--         Con "[]"
--             ([] :-> (C "List") :$$ V "a") 
--             Nothing
--       , Con "_::_" 
--             ([ "a" :@ C "Type" ] :-> (C "List") :$$ V "a") 
--             Nothing
--     ]


-- defnListText = [text|
--     data List : (a : Type) -> Type where
--         [] : List a
--         _:_ : (a : Type) -> List a
--   |]


-- defnSet :: Trm Name
-- defnSet = 
--     Data "Set" (["a" :@ C "Type"] :-> C "Type") [
--         Con "{}"
--             ( [] :-> (C "Set") :$$ V "a" ) 
--             Nothing
--       , Con "_++_" 
--             ( [ "a" :@ C "Type" ] :-> (C "Set") :$$ V "a" ) 
--             Nothing
--     ]


-- defnFOLFml :: Trm Name
-- defnFOLFml = Data "Fml" ([ Explicit Nothing $ (C "Set") :$$ (C "Name") ] :-> C "Type") [
--         Con "Atom"
--             ( [ "a" :@ C "Name" ] :-> (C "Fml") :$$ ( Refine "X" ((C "Set") :$$ (C "Name")) ((C "elem") :$ [V "a", V "X"]) ) ) 
--             Nothing
--     ]




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
    show = show . unTok
    -- show Token{..} 
    --     | rowStart == -1 || 
    --       rowEnd == -1   || 
    --       colStart == -1 ||
    --       colEnd == -1   = show unTok
    --     | otherwise = show unTok ++ " : Row (" ++ show rowStart ++ ":" ++ show rowEnd ++ "), Col (" ++ show colStart ++ ":" ++ show colEnd ++ ")"



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



startsWithRes :: [String] -> String -> Maybe (String, String)
startsWithRes xs s = foldr (\p prev -> case liftM (p,) $ prefix p s of Just x -> Just x ; Nothing -> prev) Nothing xs


break' :: MonadState (Row, Col) m => (Char -> Bool) -> String -> m (String, String)
break' _ [] = return ([], [])
break' t s@(x:xs) 
    | t x = return ([], s)
    | otherwise = do
        if x == '\n' then modify (bimap (+1) (const 0)) else modify (second (+1))
        liftM (first (x:)) $ break' t xs


startsWithRes' :: [(String, String)] -> String -> Maybe (String, String, String)
startsWithRes' xs str = foldr (\(p,s) prev -> case liftM (p,s,) $ prefix p str of Just x -> Just x ; Nothing -> prev) Nothing xs


firstOccurence :: String -> String -> (String, String)
firstOccurence _ [] = ([], [])
firstOccurence pre s@(x:xs) | (Just s') <- prefix pre s = ([], pre ++ s')
                            | otherwise = first (x:) $ firstOccurence pre xs



incrBy :: MonadState (Row, Col) m => String -> m ()
incrBy "" = return ()
incrBy ('\n':xs) = do
    modify (bimap (+1) (const 1))
    incrBy xs
incrBy (_:xs) = do
    modify (second (+1))
    incrBy xs

data TokenizerSettings = TokenizerSettings {
    reserved :: [String] -- tokens which are special
  , comment :: [(String, String)] -- ignores everything from the start token till the end, inclusive
  , block :: [(String, String)] -- like comment but keeps the whole block and the start/end tokens
  , delim :: [Char] -- parses a string of two or more characters as a delimiter, e.g. ----- or ===
  , special :: [Char] -- should include first charachter of each special token
} deriving Show

defaultTokenizerSettings :: TokenizerSettings
defaultTokenizerSettings = TokenizerSettings {
    reserved = []
  , comment = []
  , block = []
  , delim = []
  , special = []
}

tokenize :: MonadState (Row, Col) m => TokenizerSettings -> String -> m [Token Text]
tokenize _ "" = return []
tokenize ts ('\n':xs) = do
    incrBy "\n"
    tokenize ts xs
tokenize ts (x:xs) 
    | x == ' ' || x == '\t' = do
    incrBy [x]
    tokenize ts xs
tokenize ts (startsWithRes' (comment ts) -> Just (start, end, s)) = do
    incrBy start -- move by the 'start' token
    let (com, s') = firstOccurence end s -- look for the first occurence of the 'end' token
    incrBy com
    -- if we found the 'end' tag, strip it from s' and add it to the token list
    -- otherwise we must have reached the end of the string, in which case, only return the 'start' tag
    -- and 'comment' tags, as s' must be empty.
    case stripPrefix end s' of
        Just s'' -> do
            incrBy end
            tokenize ts s''
        Nothing ->
            return []
tokenize ts (startsWithRes' (block ts) -> Just (start, end, s)) = do
    (row,col) <- get -- get the current position in text
    incrBy start -- move by the 'start' token
    (startRow,startCol) <- get -- get the end of the 'start' token
    let (blck, s') = firstOccurence end s -- look for the first occurence of the 'end' token
    incrBy blck
    (blckRow,blckCol) <- get
    -- if we found the 'end' tag, strip it from s' and add it to the token list
    -- otherwise we must have reached the end of the string, in which case, only return the 'start' tag
    -- and 'comment' tags, as s' must be empty.
    case stripPrefix end s' of
        Just s'' -> do
            incrBy end
            (endRow,endCol) <- get
            let sToken = Token (toS start) row startRow col startCol
                cToken = Token (toS blck) startRow blckRow startCol blckCol
                eToken = Token (toS end) blckRow endRow blckCol endCol

            liftM ([sToken, cToken, eToken] ++) $ tokenize ts s''
        Nothing ->
            let sToken = Token (toS start) row startRow col startCol
                cToken = Token (toS blck) startRow blckRow startCol blckCol in
            return [sToken, cToken]
tokenize ts (startsWithRes (reserved ts) -> Just (p, s')) = do
    (rowS,colS) <- get
    incrBy p
    (rowE,colE) <- get
    liftM (Token (toS p) rowS rowE colS colE :) $ tokenize ts s'
tokenize ts (x:xs)
  | x `S.member` delim' = do
    (rowS,colS) <- get
    incrBy [x]
    (as, bs) <- break' (/= x) xs
    (rowE,colE) <- get
    liftM (Token (toS (x:as)) rowS rowE colS colE:) $ tokenize ts bs
  | x `S.member` special' = do
    (rowS,colS) <- get
    incrBy [x]
    liftM (Token (toS [x]) rowS rowS colS (colS+1) :) $ tokenize ts xs
  | otherwise             = do
    (rowS,colS) <- get
    incrBy [x]
    (as, bs) <- break' (`S.member` special') xs
    (rowE,colE) <- get
    liftM (Token (toS (x:as)) rowS rowE colS colE:) $ tokenize ts bs
  where
    special' = S.fromList (special ts)
    delim' = S.fromList (delim ts)




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
var :: Set Text -> Prod r e (Token Text) (Token Text)
var reserved = satisfy (\t -> 
    not ((unTok t) `S.member` reserved) &&
    T.length (unTok t) > 0 &&
    not (isDigit $ T.head (unTok t)))


-- reservedKeywords :: Set Text
-- reservedKeywords = S.fromList [
--     "(", ")", "->", ":", "=", "{", "}", "{@", "@}", "data", "where", "bind", "in" ] 
--     -- , "infixl", "infixr", "prefix", "mixfix", 
--     -- "=", ">", "<", "import", "renaming", "hiding", ] 

reservedKeywords :: Set Text
reservedKeywords = S.fromList ["(", ")", "{", "}", "{@", "@}", "|", ":", "->", "data", "where", "bind", "in"] 

bracketed :: (Eq b, IsString b) => Prod r b b a -> Prod r b b a
bracketed x = namedToken "(" *> x <* namedToken ")"

expLang :: G (Exp (Token Text))
expLang = mdo
    name    <- rule $ var reservedKeywords
    varR <- rule $ V <$> name

    appR <- rule $ 
            App <$> (appR <|> refineR <|> varR) <*> pure ExplicitApp <*> (varR <|> refineR) -- (e e) x / {@ .. @} x / x x / (e e) {@ .. @} / {@ .. @} {@ .. @} / x {@ .. @}
        <|> App <$> (appR <|> refineR <|> varR) <*> pure ExplicitApp <*> bracketed expr -- (e e) (e) / {@ .. @} (e) / x (e)
        <|> App <$> bracketed expr <*> pure ExplicitApp <*> (varR <|> refineR) -- (e) x / (e) {@ .. @}
        <|> App <$> bracketed expr <*> pure ExplicitApp <*> bracketed expr -- (e) (e)
        <|> App <$> (appR <|> refineR <|> varR) <*> (namedToken "{" *> (ImplicitNamedApp <$> name) <* namedToken "=") <*> (expr <* namedToken "}") -- e f {x = e} / {@ .. @} {x = e} / x {x = e}
        <|> App <$> bracketed arrR <*> (namedToken "{" *> (ImplicitNamedApp <$> name) <* namedToken "=") <*> (expr <* namedToken "}") -- (e -> e) {x = e}

    arrR <- rule $ 
            Arr <$> (namedToken "(" *> (ExplicitNamedArr <$> name) <* namedToken ":") <*> (expr <* namedToken ")") <*> (namedToken "->" *> expr) -- (x : e) -> e
        <|> Arr <$> (namedToken "{" *> (ImplicitNamedArr <$> name) <* namedToken ":") <*> (expr <* namedToken "}") <*> (namedToken "->" *> expr) -- {x : e} -> e
        <|> Arr <$> pure ExplicitArr <*> varR <*> (namedToken "->" *> expr) -- n -> e
        <|> Arr <$> pure ExplicitArr <*> appR <*> (namedToken "->" *> expr) -- X x1 ... xn -> e
        <|> Arr <$> pure ExplicitArr <*> refineR <*> (namedToken "->" *> expr) -- {@ ... @} -> e
        <|> Arr <$> pure ExplicitArr <*> bracketed arrR <*> (namedToken "->" *> expr) -- (e -> e) -> e

    refineR <- rule $ Refine <$> 
        (namedToken "{@" *> name <* namedToken ":") <*> expr <*> (namedToken "|" *> expr <* namedToken "@}")

    expr <- rule $ bracketed expr <|> refineR <|> arrR <|> appR <|> varR
        
    return expr


-- reservedArrType :: Set Text
-- reservedArrType = reservedKeywords `S.union` S.fromList ["(", ")", "{", "}", "{@", "@}", "|", ":"] 


-- arrTypeLang :: G (ArrType (Token Text))
-- arrTypeLang = mdo
--     name    <- rule $ var reservedKeywords
--     expR <- expLang
--     explicitR <- rule $
--             -- Explicit <$> pure Nothing <*> expR -- Exp
--         -- <|> 
--         Explicit <$> (namedToken "(" *> (Just <$> name) <* namedToken ":") <*> (expR <* namedToken ")") -- (name : Exp)
--     implicitR <- rule $
--             Implicit <$> (namedToken "{" *> name <* namedToken ":") <*> (expR <* namedToken "}") -- {name : Exp}

--     rule $ explicitR <|> implicitR

-- -- reservedType :: Set Text
-- -- reservedType = reservedKeywords `S.union` S.fromList ["(", ")", "{", "}", "{@", "@}", "|", ":", "->"] 


-- typeLang :: G (Type (Token Text))
-- typeLang = mdo
--     expR <- expLang
--     arrTypeR <- arrTypeLang
--     listR <- rule $ 
--             (:[]) <$> arrTypeR -- e
--         <|> (:) <$> (arrTypeR <* namedToken "->") <*> listR -- (e1 -> ... -> en)
--     expr <- rule $ 
--             ([]:->) <$> expR -- e
--         <|> (:->) <$> listR <*> (namedToken "->" *> expR) -- ... -> ... -> e

--     rule $ (namedToken "(" *> expr <* namedToken ")") <|> expr 



-- -- since we hava an arrow type in both Exp (Arr) and in Type (:->), we need to normalize 
-- -- parsed stuff so that we get a normal form by pulling out app possible Arr into :->
-- expToArrType :: Exp n -> ([ArrType n] , Exp n)
-- expToArrType (Arr n x y) =  
--     let (xs,e) = expToArrType y in (Explicit n x:xs,e)
-- expToArrType x = ([],x)


-- fixTypeLangParse :: Type n -> Type n
-- fixTypeLangParse (xs :-> e) = 
--     let (xs',e') = expToArrType e in (xs ++ xs') :-> e'


trmLang :: G (Trm (Token Text))
trmLang = mdo
    name    <- rule $ var reservedKeywords
    expR <- expLang
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
            expR <*> (namedToken "where" *> tyConR)
    -- declR
    return dataR
 


tokenizerSettings = defaultTokenizerSettings {
    reserved = ["{@", "@}", "->", "<=", ">="] 
  , comment = [("--", "\n")]
  , block = [("\"", "\"")]
  , special = " \n(){}[],;|<>=:&-~./\\"
}



tokenizer :: Text -> [Token Text]
tokenizer = flip evalState (1,1) . tokenize tokenizerSettings . toS



-- from :: Exp Text -> Exp Text
-- from s = case parseG tokenizer expLang $ toS $ pprint s of
--     Right res -> fmap unTok res
--     Left e -> V "error"


--     Unbound "Atom" (Arr (Just "a") (C "Name") (E $ App (C "Fml") [Refine "X" (App (C "Set") [C "Name"]) (App (C "elem") [V "a", V "X"])])),
--     Unbound "##__" (ImpArr 
--         "XS" (App (C "Set") [C "Name"])
--         (Arr 
--             (Just "a") (C "Name")
--             (Arr 
--                 Nothing (App (C "Fml") [V "XS"])
--                 (E $ App (C "Fml") [Refine "X" (App (C "Set") [C "Name"]) (App (C "eq") [V "X", App (C "diff") [V "XS", App (C "singleton") [V "a"]]])])))),
--     Unbound "#__" (ImpArr 
--         "XS" (Refine "X" (App (C "Set") [C "Name"]) (App (C "eq") [V "XS", App (C "union") [App (C "singleton") [V "a"], V "X"]]))
--         (Arr 
--             (Just "a") (C "Name")
--             (Arr 
--                 Nothing (App (C "Fml") [V "XS"])
--                 (E $ App (C "Fml") [Refine "X" (App (C "Set") [C "Name"]) (App (C "eq") [V "X", App (C "diff") [V "XS", App (C "singleton") [V "a"]]])]))))
--     ]



