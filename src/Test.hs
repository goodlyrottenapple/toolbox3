{-# LANGUAGE 
    PatternSynonyms, GADTs, ScopedTypeVariables, TupleSections, ViewPatterns, 
    FlexibleInstances, MultiParamTypeClasses, RecursiveDo, QuasiQuotes, 
    GeneralizedNewtypeDeriving, DerivingStrategies, DeriveGeneric, DeriveAnyClass, 
    DeriveFunctor, FlexibleContexts, RankNTypes, OverloadedStrings, RecordWildCards, 
    StandaloneDeriving, DeriveDataTypeable #-}

module Test where

import Core

-- import LamPi

notation =  [t3|
infix 2 ⊢
infixr 3 → , >
infixl 4 ∧, ∨, ;

-- infixr 3 

-- data Name : * where end
-- data Set : * -> * where end

data Nat : * where
	Z : Nat |
	S : Nat -> Nat
end

data Vec : Type -> Nat -> Type where
	Nil : {a : *} -> Vec a Z |
	Cons : {a : *} -> {n : Nat} -> (x : a) -> Vec a n -> Vec a (S n)
end


data Ty : * where
	Fm : Ty
  | Fnc : Ty
  | Act : Ty
  | Ag : Ty
end


data Formula : Ty -> * where
	A : String -> Formula Fm
  | (∧) : Formula Fm -> Formula Fm -> Formula Fm
  | (∨) : Formula Fm -> Formula Fm -> Formula Fm
  | (→) : Formula Fm -> Formula Fm -> Formula Fm
  | trZer : Formula Fnc -> Formula Fm -> Formula Fm
end


data Structure : Ty -> * where
	F : {t : Ty} -> Formula t -> Structure t
  | (;) : Structure Fm -> Structure Fm -> Structure Fm
  | (>) : Structure Fm -> Structure Fm -> Structure Fm
end

data (⊢) : {t : Ty} -> Structure t -> Structure t -> * where
	Atom : {s : String} -> (⊢) {Fm} (F {Fm} (A s)) (F {Fm} (A s))
  | CL : {X : Structure Fm} -> {Y : Structure Fm} -> 
		(⊢) {Fm} (X ; X) Y -> (⊢) {Fm} X Y
  | AndL : {A : Formula Fm} -> {B : Formula Fm} -> {X : Structure Fm} ->
  		(⊢) {Fm} (F {Fm} A ; F {Fm} B) X -> (⊢) {Fm} (F {Fm} (A ∧ B)) X

  | AndR : {A : Formula Fm} -> {B : Formula Fm} -> {X : Structure Fm} -> {Y : Structure Fm} ->
  		(⊢) {Fm} (F {Fm} A) X -> (⊢) {Fm} (F {Fm} B) Y -> (⊢) {Fm} (X ; Y) (F {Fm} (A ∧ B)) 

-- X |- A    Y |- B
-- ---------------- andR ("\land_R")
-- X , Y |- A /\ B
end
|]