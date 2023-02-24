{-# OPTIONS --cubical #-}
module Structures where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
--open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
open import Weakening
open import Values
open import NormalForm
open import EvalSpec
open import Stability
open import TypeEval
open import TermInfo
open import SCVA
open import EvaluatorSC
open import Evaluator

private variable n : ℕ

cnat : {X : Con} → Ty (suc n) X
cnat {n} = Pi (Pi (U n) (U n)) (Pi (U n) (U n))

czero : ∀{G} → Tm (suc n) G cnat
czero = lam (lam (subst (Tm _ _) U[] (π₂ idt)))

norm-czero = termination {n = suc zero} {X = ∅} {u = czero}


--csuc : ∀{G} → Tm G (cnat ⇒ cnat)
--csuc = lam (lam (lam (vs vz $ (vs (vs vz) $ vs vz $ vz))))

--ctwo : ∀{G} → Tm G cnat
--ctwo = csuc $ (csuc $ czero)
