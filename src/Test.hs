{-# LANGUAGE 
    PatternSynonyms, GADTs, ScopedTypeVariables, TupleSections, ViewPatterns, 
    FlexibleInstances, MultiParamTypeClasses, RecursiveDo, QuasiQuotes, 
    GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric, DeriveAnyClass, 
    DeriveFunctor, FlexibleContexts, RankNTypes, OverloadedStrings, RecordWildCards, 
    StandaloneDeriving, DeriveDataTypeable, TypeApplications #-}

module Test where

import Core

import LamPi

import Control.Monad(foldM)
import Control.Monad.Except
import           Text.Earley

import qualified Data.Map as M
import Data.Text(Text)
import Data.Bifunctor(bimap)
import Data.String.Conv
import Data.List(intercalate, elemIndex)

-- main = [t3|
-- infixl 1 &&
-- infix 2 ∈ , ∉, ≡
-- infix 3 \\ , \
-- infixl 4 ∪, ∩

-- data (∈) : {a : Type} -> a -> Set a -> Prop where end
-- data (∉) : {a : Type} -> a -> Set a -> Prop where end
-- data (≡) : {a : Type} -> a -> a -> Prop where end
-- data (\\) : {a : Type} -> Set a -> a -> Set a where end
-- data (∪) : {a : Type} -> Set a -> Set a -> Set a where end
-- data (∩) : {a : Type} -> Set a -> Set a -> Set a where end
-- data (\) : {a : Type} -> Set a -> Set a -> Set a where end
-- data singleton : {a : Type} -> a -> Set a where end
-- data ¬ : Prop -> Prop where end
-- data (&&) : Prop -> Prop -> Prop where end
-- data infer : {a : Type} -> a -> Prop where end
-- |]

test = [t3|
{-# SMT-command ('set-logic 'QF_UFSLIAFS) #-}
{-# SMT-log-enabled true #-}
{-# SMT-log-level 1 #-}

infixl 1 &&
infix 2 ⊢ , ∈ , ∉, ≡, ⩸, ⩵
infix 3 \\ , \
infixr 3 → , -< , >, ∷, $
infixl 4 ∧, ∨, ;, ∪, ∩


smt-def (∈) : {a : Type} -> (x : a) -> (X : Set a) -> Prop where
  (member x X)
end

smt-def (∉) : {a : Type} -> (x : a) -> (X : Set a) -> Prop where
  (not (member x X))
end

smt-def singleton : {a : Type} -> (x : a) -> Set a where 
  (singleton x)
end

smt-def (≡) : {a : Type} -> (x : a) -> (y : a) -> Prop where 
  ('= x y)
end

smt-def (∪) : {a : Type} -> (X : Set a) -> (Y : Set a) -> Set a where 
  (union X Y)
end

smt-def (∩) : {a : Type} -> (X : Set a) -> (Y : Set a) -> Set a where 
  (intersection X Y)
end

smt-def (\\) : {a : Type} -> (X : Set a) -> (x : a) -> Set a where 
  (setminus X (singleton x))
end

smt-def (\) : {a : Type} -> (X : Set a) -> (Y : Set a) -> Set a where 
  (setminus X Y)
end


smt-def infer : {a : Type} -> (x : a) -> Prop where 
  ('= x x)
end

smt-def (&&) : (X : Prop) -> (Y : Prop) -> Prop where 
  ('and X Y)
end

smt-def ¬ : (X : Prop) -> Prop where 
  ('- X)
end

data Nat : * where
    0 : Nat |
    Suc : Nat -> Nat
end


data Vec : Type -> Nat -> Type where
  NilV : {a : Type} -> Vec a 0 |
  ConsV : {a : Type} -> {n : Nat} -> a -> Vec a n -> Vec a (Suc n)
end

language LaTeX


translation Vec to LaTeX where
  NilV -> '''\varempty''' |
  ConsV a v -> "\cons{#a}{#v}"
end

data List : Set Name -> (Set Name -> *) -> * where
    ∅ : -- {𝓝 : Set Name} -> [infer 𝓝] -> -- this is a bit of a hack to force the SMT solver to come up with X automatically
        {τ : Set Name -> *} -> List {| |} τ
  | (∷) : {X : Set Name} -> {Y : Set Name} -> {Z : Set Name} -> {τ : Set Name -> *} -> 
        (x : τ X) -> List Y τ -> [Z ≡ X ∪ Y] -> List Z τ
end

translation List to LaTeX where
    ∅ -> ""
  | (∷) x xs -> "#{x} , #{xs}"
end

data Trm : Set Name -> * where 
    var : {𝓝 : Set Name} -> (n : Name) -> [n ∈ 𝓝] -> Trm 𝓝
  | const : {𝓝 : Set Name} -> Name -> Trm 𝓝
  | fun : {𝓝 : Set Name} -> Name -> List 𝓝 Trm -> Trm 𝓝
end

def empty : List {| |} Trm where
  ∅
end


data SubstList : Set Name -> Set Name -> (Set Name -> *) -> * where
    Nil : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> {τ : Set Name -> *} -> SubstList 𝓝 𝓝₂ τ
  | Cons : {𝓝 : Set Name} -> 
        {𝓝₁₁ : Set Name} -> {𝓝₂₁ : Set Name} -> 
        {𝓝₁₂ : Set Name} -> {𝓝₂₂ : Set Name} -> 
        {τ : Set Name -> *} ->
        (x : Name) -> 
        -- [ x ∉ 𝓝 && x ∉ 𝓝₁₁ && x ∉ 𝓝₂₁ ] -> 
        [ x ∉ 𝓝 && x ∉ 𝓝₁₁ ] -> 
        (s : τ 𝓝) -> SubstList 𝓝₁₁ 𝓝₂₁ τ -> 
        [𝓝₁₂ ≡ 𝓝₁₁ ∪ (singleton x) && 𝓝₂₂ ≡ 𝓝₂₁ ∪ 𝓝] -> 
        SubstList 𝓝₁₂ 𝓝₂₂ τ
end


data F : Set Name -> * where
    R : Name -> {𝓝 : Set Name} -> List 𝓝 Trm -> F 𝓝
  | (⩵) : {𝓝 : Set Name} -> Trm 𝓝 -> Trm 𝓝 -> F 𝓝
  | ⊤ : {𝓝 : Set Name} -> F 𝓝
  | ⊥ : {𝓝 : Set Name} -> F 𝓝
  | (∧) : {𝓝 : Set Name} -> F 𝓝 -> F 𝓝 -> F 𝓝
  | (∨) : {𝓝 : Set Name} -> F 𝓝 -> F 𝓝 -> F 𝓝
  | (→) : {𝓝 : Set Name} -> F 𝓝 -> F 𝓝 -> F 𝓝
  | (-<) : {𝓝 : Set Name} -> F 𝓝 -> F 𝓝 -> F 𝓝
  | ∀ : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> (x : Name) -> [ x ∈ 𝓝 ] -> F 𝓝 -> [ 𝓝₂ ≡ 𝓝 \\ x ] -> F 𝓝₂
  | ∃ : (x : Name) -> {𝓝 : Set Name} -> [ x ∈ 𝓝 ] -> F 𝓝 -> {𝓝₂ : Set Name} -> [ 𝓝₂ ≡ 𝓝 \\ x ] -> F 𝓝₂
  | ∘ : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> (x : Name) -> [ x ∉ 𝓝 ] -> F 𝓝 -> [ 𝓝₂ ≡ 𝓝 ∪ (singleton x) ] -> F 𝓝₂
  | subst : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> SubstList 𝓝 𝓝₂ Trm -> F 𝓝 -> F 𝓝₂
end

translation F to LaTeX where
    R n lst -> "#{n}(#{lst})"
  | (⩵) a b -> "#{a} = #{b}"
  | ⊤ -> "\top"
  | ⊥ -> "\bot"
  | (∧) a b -> "#{a} \wedge #{b}"
  | (∨) a b -> "#{a} \vee #{b}"
  | (→) a b -> "#{a} \to #{b}"
  | ∀ x a -> "\all#{x}.\,#{a}"
end

data S : Set Name -> * where
    ↑ : {𝓝 : Set Name} -> F 𝓝 -> S 𝓝
  | Ieq : {𝓝 : Set Name} -> Trm 𝓝 -> Trm 𝓝 -> S 𝓝
  | I : {𝓝 : Set Name} -> S 𝓝
  | IR : Name -> {𝓝 : Set Name} -> List 𝓝 Trm -> S 𝓝
  | (;) : {𝓝 : Set Name} -> S 𝓝 -> S 𝓝 -> S 𝓝
  | (>) : {𝓝 : Set Name} -> S 𝓝 -> S 𝓝 -> S 𝓝
  
  | Q : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> (x : Name) -> [ x ∈ 𝓝 ] -> S 𝓝 -> [ 𝓝₂ ≡ 𝓝 \\ x ] -> S 𝓝₂
  | ⊙ : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> (x : Name) -> [ x ∉ 𝓝 ] -> S 𝓝 -> [ 𝓝₂ ≡ 𝓝 ∪ (singleton x) ] -> S 𝓝₂
  | substS : {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> SubstList 𝓝₂ 𝓝₂ Trm -> S 𝓝 -> S 𝓝₂
end


translation S to LaTeX where
    ↑ f -> "#{f}"
  | I -> "\mathbb{I}"
  | IR n lst -> "\bf{#{n}}(#{lst})"
  | (;) s t -> "#{s} ; #{t}"
  | (>) s t -> "#{s} > #{t}"
  | Q x s -> "\bf{Q}#{x}.\,#{s}"
end


data (⊢) : {𝓝 : Set Name} -> S 𝓝 -> S 𝓝 -> Type where
  IdIR    : {r : Name} -> {𝓝 : Set Name} -> {ts : List 𝓝 Trm} -> 

            --------------------
            IR r ts ⊢ ↑ (R r ts) 
  |
  AllR    : {𝓝ₓ : Set Name} -> {𝓝ₐ : Set Name} -> 
            {X : S 𝓝ₓ} -> {x : Name} -> {A : F 𝓝ₐ} -> 

          X ⊢ Q x (↑ A) ->
          -------------
          X ⊢ ↑ (∀ x A)
  | 
  Q⊙Disp  : {𝓝ₓ : Set Name} -> {𝓝ᵧ : Set Name} -> 
            {X : S 𝓝ₓ} -> {Y : S 𝓝ᵧ} -> {x : Name} ->

            Y ⊢ Q x X ->
            ---------
            ⊙ x Y ⊢ X
  | 
  Q⊙Disp2 : {𝓝ₓ : Set Name} -> {𝓝ᵧ : Set Name} -> 
            {X : S 𝓝ₓ} -> {Y : S 𝓝ᵧ} -> {x : Name} ->

            (⊙ x Y) ⊢ X ->
            -----------
            Y ⊢ (Q x X)
  | 
  ∘R :     {𝓝ₓ : Set Name} -> {𝓝ₐ : Set Name} -> 
         {X : S 𝓝ₓ} -> {x : Name} -> {A : F 𝓝ₐ} -> 

           X ⊢ ⊙ x (↑ A) ->
           -------------
           X ⊢ ↑ (∘ x A)
  | 
  ⊙mon :   {𝓝 : Set Name} -> {𝓝₂ : Set Name} -> 
           {X : S 𝓝} -> {Y : S 𝓝} -> {x : Name} ->

                  X ⊢ Y -> 
         -----------------------
         ⊙ {𝓝} {𝓝₂} x X ⊢ ⊙ x Y
  | 
  IRL :    {r : Name} -> {𝓝 : Set Name} -> 
           {X : S 𝓝} -> {ts : List 𝓝 Trm} -> 

         IR r ts ⊢ X ->
         --------------
         ↑ (R r ts) ⊢ X
 --  | CL : {X : Sucture 'Fm} -> {Y : Sucture 'Fm} -> 
    --  X ; X ⊢ Y -> X ⊢ Y
 --  | AndL : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Sucture 'Fm} ->
 --         F A ; F B ⊢ X -> F (A ∧ B) ⊢ X
 --  | AndR : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Sucture 'Fm} -> {Y : Sucture 'Fm} ->
 --         F A ⊢ X -> F B ⊢ Y -> 
 --         ------------------
 --         X ; Y ⊢ F (A ∧ B)
end


translation (⊢) to LaTeX where
  IdIR : x ⊢ y -> "\AXC{}\UIC{#{x} \vdash #{y}}\RightLabel{IdIR}"
end


-- def a : IR 'empty ∅ ⊢ ↑ (R 'empty ∅) where
--  a = IdIR -- {'empty} {{| |}} {∅ } 
--  end

def b = IdIR {'empty} {{| |}} {∅} end

translate b to LaTeX end


-- def testFBad = subst (Cons 'x (const '0) (Cons 'y (var 'y) Nil)) (R '+ (var 'x ∷ var 'y ∷ ∅)) end
def testF = subst 
                (Cons 
                    'x (const '0) 
                (Cons 
                    'y (var 'z) 
                Nil)) 
                (R '+ (var 'x ∷ var 'y ∷ ∅)) -- [x -> 0, y -> z](x+y)
end

-- def test2 = IR '+ {?} ? end


-- def idTest : IR '+ ∅ ⊢ ↑ (R '+ ∅) where
--     idTest = IdIR
-- end



-- 'X ⊢ ∀ 'x (∘'x 'X)

def lemma : ↑(R 'X ∅) ⊢ ↑(∀ 'x (∘ 'x (R 'X ∅))) where
  (AllR (Q⊙Disp2 (∘R (⊙mon (IRL IdIR))))) -- (AllR (Q⦿Disp2 (∘R (⦿mon (IRL IdIR)))))
end


-- def lemma2a : ↑(R 'X ∅) ⊢ ↑(∀ 'x (R 'X ∅)) where
--     lemma2a = AllR ?
-- end



-- def test : {F : Set Name} -> {F1 : Set Name} -> (X : F F) -> (x : Name) ->
--     (↑ X) ⊢ (↑ (∀ {F1} {F} x (∘ {F} {F1} x X))) where
--     test = ?
-- end


-- def test2 : Trm {| 'y, 'x, 'x |} where
--     test2 = ? --var 'y
-- end


-- def test2a : Trm _ where
--     test2a = var 'y
-- end



-- data stupid : Name -> * where
--     stupidC : {n : Name} -> stupid n
-- end


-- def test3 : stupid 'a where
--     test3 = stupidC
-- end

-- -- def lemma2 : ⦿ 'x (↑(R 'X ∅)) ⊢ (↑ (∘ 'x (R 'X ∅))) where
-- --     lemma2 = ∘R ?
-- -- end

-- -- def lemma2 : ⦿ 'x (↑(R 'X ∅)) ⊢ (⦿ 'x (↑ (R 'X ∅))) where
-- --     lemma2 = ? -- (⦿mon ?)
-- -- end



-- data (⩸) : {A : *} -> A -> A -> * where
--     refl : {A : *} -> {a : A} -> a ⩸ a
-- end


-- def test4 : {|'x, 'y|} ⩸ {|'x, 'y, 'x|} where
--     test4 = refl
-- end



|]


-- elab_main = do
--     r <- runExceptT $ foldM (defineDecl @(ExceptT Sing IO) True) (Γ []) main
--     case r of
--         Left e -> do
--             putSLn e
--             return $ Γ []
--         Right g -> return g




elab_test = do
    -- g <- elab_main
    -- putStrLn $ show test
    r <- runExceptT $ foldM (defineDecl @(ExceptT String IO) True) emptyΓ test
    case r of
        Left e -> putStrLn e
        Right g -> putStrLn $ show g


elab printSummary fName = do
  s <- readFile fName
  let start_loc = bimap Row Col (0,0)
  case parseG (pretokenize start_loc) infixLang $ toS s of
      Right is -> do
          let tokens = tokenize start_loc is $ toS s
          -- putStrLn $ show tokens
          case parseG'' (tokenize start_loc is) (declLang is) $ toS s of
              ([], Report{..}) -> fail $ mkError $ tokens !! position
              ([x],_) -> case runSTE $ makeDecl x of
                  Left e -> fail $ "converting to LambPi failed with error:\n" ++ e
                  Right output -> do
                    -- putStrLn $ show output
                    r <- runExceptT $ 
                      foldM 
                        (defineDecl @(ExceptT String IO) True) 
                        emptyΓ{infixM = M.fromList $ map (\x@Infix{..} -> (symb, x)) is} 
                        output
                    case r of
                        Left e -> putStrLn e
                        Right g -> if printSummary then putStrLn $ show g else pure () -- 
                  -- putStrLn "\nParsed and pretty printed output:\n"
                  -- putStrLn $ pprint $ map (declMap unTok) x
              (xs,_) -> fail $ "Ambiguous parse:\n" ++ (intercalate "\n" $ map (Core.pprint) (xs :: [[Core.Decl (Token Text)]]))
      Left e -> fail $ "Infix preprocessing failed:\n" ++ show e
    
  where 
    mkError :: Token Text -> String
    mkError (Token{..}) = 
        "Parsing error at " ++ toS unTok ++ 
        " (line " ++ show rowStart ++ ", column " ++ show colStart ++ ")"

-- runElabType0 g $ C "∀" :@: [E $ MkName "x",  E $ C "base"]