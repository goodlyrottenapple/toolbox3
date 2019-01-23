{-# LANGUAGE 
    PatternSynonyms, GADTs, ScopedTypeVariables, TupleSections, ViewPatterns, 
    FlexibleInstances, MultiParamTypeClasses, RecursiveDo, QuasiQuotes, 
    GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric, DeriveAnyClass, 
    DeriveFunctor, FlexibleContexts, RankNTypes, OverloadedStrings, RecordWildCards, 
    StandaloneDeriving, DeriveDataTypeable #-}

module Test where

import Core

import LamPi

import Control.Monad(foldM)
import Control.Monad.Except

test = [t3|
infix 2 ⊢ , ∈ , ≡
infix 3 \\ , \
infixr 3 → , >, $
infixl 4 ∧, ∨, ;, ∪, ∩

-- infixr 3 

-- data Name : * where end
-- data Set : * -> * where end

data Nat : * where
    0 : Nat |
    S : Nat -> Nat
end

data Vec : * -> Nat -> * where
    Nil : {T : *} -> Vec T 0 |
    ($) : {T : *} -> {n : Nat} -> (x : T) -> Vec T n -> Vec T (S n)
end



data Formula : Name -> * where
    A : {n : Name} -> Name -> Formula n
  | (∧) : Formula 'Fm -> Formula 'Fm -> Formula 'Fm
  -- | (∨) : Formula Fm -> Formula Fm -> Formula Fm
  -- | (→) : Formula Fm -> Formula Fm -> Formula Fm
  | trZer : Formula 'Fnc -> Formula 'Fm -> Formula 'Fm
end


data Structure : Name -> * where
    F : {t : Name} -> Formula t -> Structure t
  | (;) : Structure 'Fm -> Structure 'Fm -> Structure 'Fm
--   | (>) : Structure Fm -> Structure Fm -> Structure Fm
end

data (⊢) : {t : Name} -> Structure t -> Structure t -> * where
    Atom : {a : Name} -> {t : Name} -> F (A {t} a) ⊢ F (A a)
 --  | CL : {X : Structure 'Fm} -> {Y : Structure 'Fm} -> 
    --  X ; X ⊢ Y -> X ⊢ Y
 --  | AndL : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} ->
 --         F A ; F B ⊢ X -> F (A ∧ B) ⊢ X
 --  | AndR : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} -> {Y : Structure 'Fm} ->
 --         F A ⊢ X -> F B ⊢ Y -> 
 --         ------------------
 --         X ; Y ⊢ F (A ∧ B)
end


-- data Set : * -> * where end
data (∈) : {a : Type} -> a -> Set a -> Prop where end
data (≡) : {a : Type} -> a -> a -> Prop where end
data (\\) : {a : Type} -> Set a -> a -> Set a where end
data (∪) : {a : Type} -> Set a -> Set a -> Set a where end
data (∩) : {a : Type} -> Set a -> Set a -> Set a where end
data (\) : {a : Type} -> Set a -> Set a -> Set a where end
data singleton : {a : Type} -> a -> Set a where end


data Fml : Set Name -> * where
    base : {X : Set Name} -> Fml X
  | ∀ : (x : Name) -> {X : Set Name} -> [ x ∈ X ] -> Fml X -> {Y : Set Name} -> [ Y ≡ X \\ x ] -> Fml Y
end

def test1 = 'a $ 'b $ Nil end
def test2 = ∀ 'x base end

|]

test_elab = do
    runExceptT $ foldM (defineDecl @(ExceptT String IO) True) (Γ []) test
    return ()


-- runElabType0 g $ C "∀" :@: [E $ MkName "x",  E $ C "base"]