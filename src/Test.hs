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

test = [t3|
infix 2 ⊢ , ∈ 
infixr 3 → , >
infixl 4 ∧, ∨, ;

-- infixr 3 

-- data Name : * where end
-- data Set : * -> * where end

data Nat : * where
	0 : Nat |
	S : Nat -> Nat
end

data Vec : * -> Nat -> * where
	Nil : {T : *} -> Vec T 0 |
	Cons : {T : *} -> {n : Nat} -> (x : T) -> Vec T n -> Vec T (S n)
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
	-- 	X ; X ⊢ Y -> X ⊢ Y
 --  | AndL : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} ->
 --  		F A ; F B ⊢ X -> F (A ∧ B) ⊢ X
 --  | AndR : {A : Formula 'Fm} -> {B : Formula 'Fm} -> {X : Structure 'Fm} -> {Y : Structure 'Fm} ->
 --  		F A ⊢ X -> F B ⊢ Y -> 
 --  		------------------
 --  		X ; Y ⊢ F (A ∧ B)
end


data Set : * -> * where end
data (∈) : {a : Type} -> a -> Set a -> Prop where end

data Fml : Set Name -> * where
	base : {X : Set Name} -> Fml X
  | all : (x : Name) -> {X : Set Name} -> [ x ∈ X ] -> Fml X -> {Y : Set Name} -> [ x ∈ X ] -> Fml Y
end

|]

(Right g) = runSTE $ foldM defineDecl (Γ []) test


-- runElabType0 g $ C "all" :@: [E $ MkName "x",  E $ C "base"]