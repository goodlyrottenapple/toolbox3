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
infixl 1 &&
infix 2 ⊢ , ∈ , ∉, ≡, ⩸, ⩵
infix 3 \\ , \
infixr 3 → , -< , >, ∷, $
infixl 4 ∧, ∨, ;, ∪, ∩



data (∈) : {a : Type} -> a -> Set a -> Prop where end
data (∉) : {a : Type} -> a -> Set a -> Prop where end
data (≡) : {a : Type} -> a -> a -> Prop where end
data (\\) : {a : Type} -> Set a -> a -> Set a where end
data (∪) : {a : Type} -> Set a -> Set a -> Set a where end
data (∩) : {a : Type} -> Set a -> Set a -> Set a where end
data (\) : {a : Type} -> Set a -> Set a -> Set a where end
data singleton : {a : Type} -> a -> Set a where end
data ¬ : Prop -> Prop where end
data (&&) : Prop -> Prop -> Prop where end
data infer : {a : Type} -> a -> Prop where end


data Nat : * where
    0 : Nat |
    S : Nat -> Nat
end

-- data Vec : * -> Nat -> * where
--     Nil : {T : *} -> Vec T 0 |
--     ($) : {n : Nat} -> {T : *} -> (x : T) -> Vec T n -> Vec T (S n)
-- end

-- def test = ($) {_} {Nat} 0 Nil end 



-- data Formula : Name -> * where
--     A : {n : Name} -> Name -> Formula n
--   | (∧) : Formula 'Fm -> Formula 'Fm -> Formula 'Fm
--   -- | (∨) : Formula Fm -> Formula Fm -> Formula Fm
--   -- | (→) : Formula Fm -> Formula Fm -> Formula Fm
--   | trZer : Formula 'Fnc -> Formula 'Fm -> Formula 'Fm
-- end


-- data Structure : Name -> * where
--     F : {t : Name} -> Formula t -> Structure t
--   | (;) : Structure 'Fm -> Structure 'Fm -> Structure 'Fm
-- --   | (>) : Structure Fm -> Structure Fm -> Structure Fm
-- end

-- data (⊢) : {t : Name} -> Structure t -> Structure t -> * where
--     Atom : {a : Name} -> {t : Name} -> F (A {t} a) ⊢ F (A a)
--  --  | CL : {X : Structure 'Fm} -> {Y : Structure 'Fm} -> 
--     --  X ; X ⊢ Y -> X ⊢ Y
--  --  | AndL : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} ->
--  --         F A ; F B ⊢ X -> F (A ∧ B) ⊢ X
--  --  | AndR : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} -> {Y : Structure 'Fm} ->
--  --         F A ⊢ X -> F B ⊢ Y -> 
--  --         ------------------
--  --         X ; Y ⊢ F (A ∧ B)
-- end


-- data Set : * -> * where end


data List : Set Name -> (T : Set Name -> *) -> * where
    ∅ : {X : Set Name} -> [infer X] -> -- this is a bit of a hack to force the SMT solver to come up with X automatically
        {T : Set Name -> *} -> List X T
  | (∷) : {X : Set Name} -> {Y : Set Name} -> {Z : Set Name} -> {T : Set Name -> *} -> 
        (x : T X) -> List Y T -> [Z ≡ X ∪ Y] -> List Z T
end

data Trm : Set Name -> * where 
    var : {F : Set Name} -> (n : Name) -> [n ∈ F] -> Trm F
  | const : {F : Set Name} -> Name -> Trm F
  | fun : {F : Set Name} -> Name -> List F Trm -> Trm F
end


data SubstList : Set Name -> Set Name -> (T : Set Name -> *) -> * where
    Nil : {F : Set Name} -> {F₂ : Set Name} -> {T : Set Name -> *} -> SubstList F F₂ T
  | Cons : {F : Set Name} -> 
        {F₁₁ : Set Name} -> {F₂₁ : Set Name} -> 
        {F₁₂ : Set Name} -> {F₂₂ : Set Name} -> 
        {T : Set Name -> *} ->
        (x : Name) -> 
        -- [ x ∉ F && x ∉ F₁₁ && x ∉ F₂₁ ] -> 
        [ x ∉ F && x ∉ F₁₁ ] -> 
        (s : T F) -> SubstList F₁₁ F₂₁ T -> 
        [F₁₂ ≡ F₁₁ ∪ (singleton x) && F₂₂ ≡ F₂₁ ∪ F] -> 
        SubstList F₁₂ F₂₂ T
end


data Fml : Set Name -> * where
    R : Name -> {F : Set Name} -> List F Trm -> Fml F
  | (⩵) : {F : Set Name} -> Trm F -> Trm F -> Fml F
  | ⊤ : {F : Set Name} -> Fml F
  | ⊥ : {F : Set Name} -> Fml F
  | (∧) : {F : Set Name} -> Fml F -> Fml F -> Fml F
  | (∨) : {F : Set Name} -> Fml F -> Fml F -> Fml F
  | (→) : {F : Set Name} -> Fml F -> Fml F -> Fml F
  | (-<) : {F : Set Name} -> Fml F -> Fml F -> Fml F
  | ∀ : {F : Set Name} -> {F2 : Set Name} -> (x : Name) -> [ x ∈ F ] -> Fml F -> [ F2 ≡ F \\ x ] -> Fml F2
  | ∃ : (x : Name) -> {F : Set Name} -> [ x ∈ F ] -> Fml F -> {F2 : Set Name} -> [ F2 ≡ F \\ x ] -> Fml F2
  | ∘ : {F : Set Name} -> {F2 : Set Name} -> (x : Name) -> [ x ∉ F ] -> Fml F -> [ F2 ≡ F ∪ (singleton x) ] -> Fml F2
  | subst : {F : Set Name} -> {F2 : Set Name} -> SubstList F F2 Trm -> Fml F -> Fml F2
end

data Str : Set Name -> * where
    ↑ : {F : Set Name} -> Fml F -> Str F
  | Ieq : {F : Set Name} -> Trm F -> Trm F -> Str F
  | I : {F : Set Name} -> Str F
  | IR : Name -> {F : Set Name} -> List F Trm -> Str F
  | (;) : {F : Set Name} -> Str F -> Str F -> Str F
  | (>) : {F : Set Name} -> Str F -> Str F -> Str F
  
  | Q : {F : Set Name} -> {F2 : Set Name} -> (x : Name) -> [ x ∈ F ] -> Str F -> [ F2 ≡ F \\ x ] -> Str F2
  | ⦿ : {F : Set Name} -> {F2 : Set Name} -> (x : Name) -> [ x ∉ F ] -> Str F -> [ F2 ≡ F ∪ (singleton x) ] -> Str F2
  | substS : {F : Set Name} -> {F2 : Set Name} -> SubstList F F2 Trm -> Str F -> Str F2
end


data (⊢) : {F : Set Name} -> Str F -> Str F -> * where
    -- Atom : {a : Name} -> {t : Set Name} -> F (A {t} a) ⊢ F (A a)
    IdIR : {r : Name} -> {F : Set Name} -> {ts : List F Trm} -> 
        IR r ts ⊢ ↑ (R r ts)

  | AllR : {F : Set Name} -> {FA : Set Name} -> {X : Str F} -> {x : Name} -> {A : Fml FA} -> 
        X ⊢ Q x (↑ A) ->
        -------------
        X ⊢ ↑ (∀ x A)

  | Q⦿Disp : {F₁ : Set Name} -> {F₂ : Set Name} -> {X : Str F₁} -> {Y : Str F₂} -> {x : Name} ->
        Y ⊢ Q x X ->
        ---------
        ⦿ x Y ⊢ X
  | Q⦿Disp2 : {F₁ : Set Name} -> {F₂ : Set Name} -> {X : Str F₁} -> {Y : Str F₂} -> {x : Name} ->
        (⦿ x Y) ⊢ X ->
        -----------
        Y ⊢ (Q x X)
  | ∘R : {FX : Set Name} -> {FA : Set Name} -> {X : Str FX} -> {x : Name} -> {A : Fml FA} -> 
        X ⊢ ⦿ x (↑ A)
     -> -------------
        X ⊢ ↑ (∘ x A)
  | ⦿mon : {F : Set Name} -> {F2 : Set Name} -> {X : Str F} -> {Y : Str F} -> {x : Name} ->
                 X ⊢ Y
     -> -----------------------
        ⦿ {F} {F2} x X ⊢ ⦿ x Y

  | IRL : {r : Name} -> {F : Set Name} -> {X : Str F} -> {ts : List F Trm} -> 
        IR r ts ⊢ X ->
        --------------
        ↑ (R r ts) ⊢ X

 --  | CL : {X : Structure 'Fm} -> {Y : Structure 'Fm} -> 
    --  X ; X ⊢ Y -> X ⊢ Y
 --  | AndL : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} ->
 --         F A ; F B ⊢ X -> F (A ∧ B) ⊢ X
 --  | AndR : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} -> {Y : Structure 'Fm} ->
 --         F A ⊢ X -> F B ⊢ Y -> 
 --         ------------------
 --         X ; Y ⊢ F (A ∧ B)
end


-- def testFmlBad = subst (Cons 'x (const '0) (Cons 'y (var 'y) Nil)) (R '+ (var 'x ∷ var 'y ∷ ∅)) end
def testFml = subst 
                (Cons 
                    'x (const '0) 
                (Cons 
                    'y (var 'z) 
                Nil)) 
                (R '+ (var 'x ∷ var 'y ∷ ∅)) -- [x -> 0, y -> z](x+y)
end

-- -- def test2 = IR '+ {?} ? end


-- def idTest : IR '+ ∅ ⊢ ↑ (R '+ ∅) where
--     idTest = IdIR
-- end



-- 'X ⊢ ∀ 'x (∘'x 'X)

def lemma : ↑(R 'X ∅) ⊢ ↑(∀ 'x (∘ 'x (R 'X ∅))) where
    lemma = (AllR (Q⦿Disp2 (∘R (⦿mon (IRL IdIR))))) -- (AllR (Q⦿Disp2 (∘R (⦿mon (IRL IdIR)))))
end


def lemma2a : ↑(R 'X ∅) ⊢ ↑(∀ 'x (R 'X ∅)) where
    lemma2a = AllR ?
end



def test : {F : Set Name} -> {F1 : Set Name} -> (X : Fml F) -> (x : Name) ->
    (↑ X) ⊢ (↑ (∀ {F1} {F} x (∘ {F} {F1} x X))) where
    test = ?
end


def test2 : Trm {| 'y, 'x, 'x |} where
    test2 = ? --var 'y
end


def test2a : Trm _ where
    test2a = var 'y
end



data stupid : Name -> * where
    stupidC : {n : Name} -> stupid n
end


def test3 : stupid 'a where
    test3 = stupidC
end

-- def lemma2 : ⦿ 'x (↑(R 'X ∅)) ⊢ (↑ (∘ 'x (R 'X ∅))) where
--     lemma2 = ∘R ?
-- end

-- def lemma2 : ⦿ 'x (↑(R 'X ∅)) ⊢ (⦿ 'x (↑ (R 'X ∅))) where
--     lemma2 = ? -- (⦿mon ?)
-- end



data (⩸) : {A : *} -> A -> A -> * where
    refl : {A : *} -> {a : A} -> a ⩸ a
end


def test4 : {|'x, 'y|} ⩸ {|'x, 'y, 'x|} where
    test4 = refl
end

|]


-- elab_main = do
--     r <- runExceptT $ foldM (defineDecl @(ExceptT String IO) True) (Γ []) main
--     case r of
--         Left e -> do
--             putStrLn e
--             return $ Γ []
--         Right g -> return g




elab_test = do
    -- g <- elab_main
    r <- runExceptT $ foldM (defineDecl @(ExceptT String IO) True) (Γ []) test
    case r of
        Left e -> putStrLn e
        Right g -> return ()


-- runElabType0 g $ C "∀" :@: [E $ MkName "x",  E $ C "base"]