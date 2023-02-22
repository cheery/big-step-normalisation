{-# OPTIONS --cubical #-}
module Proposition where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Induction.WellFounded
open import Cubical.Foundations.Isomorphism
open import Agda.Primitive
open import Library
open import Syntax

private variable n : ℕ

-- If the codomain of the function (the motives) is a mere proposition,
-- the eliminator becomes simpler as one needs not to provide any path constructor.
record Motives {l} : Set (Agda.Primitive.lsuc l) where
  field
    Tmsᴹ : {X Y : Con} → Tms X Y → Set l
    Tmᴹ : {n : ℕ} {X : Con} {A : Ty n X} → Tm n X A → Set l
    Tyᴹ : {n : ℕ} {X : Con} → Ty n X → Set l

  term-motive : {i : term-index} (u : term i) → Set l
  term-motive {Tms-i X Y} = Tmsᴹ
  term-motive {Tm-i n X A} = Tmᴹ
  term-motive {Ty-i n X} = Tyᴹ

record Methods {l} (M : Motives {l}) : Set (Agda.Primitive.lsuc l) where
  open Motives M
  infixr 10 _,ᴹ_
  infixr 20 _∘tᴹ_
  infixl 30 _[_]ᴹ
  field
    -- Type methods
    _[_]Tᴹ : {X Y : Con} {A : Ty n Y} {p : Tms X Y}
           → Tyᴹ A → Tmsᴹ p → Tyᴹ (A [ p ]T)
    Uᴹ : {X : Con} {n : ℕ} → Tyᴹ (U {X = X} n)
    Elᴹ : {X : Con} {t : Tm (suc n) X (U n)} → Tmᴹ t → Tyᴹ (El t)
    Piᴹ : {X : Con} {A : Ty n X} {B : Ty n (X , A)}
        → Tyᴹ A → Tyᴹ B → Tyᴹ (Pi A B)
    --Lᴹ : {X : Con} {A : Ty n X}
    --   → Tyᴹ A → Tyᴹ (L A)
    -- Substitution methods
    idtᴹ : {X : Con} → Tmsᴹ (idt {X = X})
    _∘tᴹ_ : {X Y Z : Con} {p : Tms Y Z} {v : Tms X Y}
          → Tmsᴹ p → Tmsᴹ v → Tmsᴹ (p ∘t v)
    εᴹ : {X : Con} → Tmsᴹ (ε {X = X})
    _,ᴹ_ : {X Y : Con} {A : Ty n Y} {p : Tms X Y} {u : Tm n X (A [ p ]T)}
         → Tmsᴹ p → Tmᴹ u → Tmsᴹ (p , u)
    π₁ᴹ : {X Y : Con} {A : Ty n Y} {p : Tms X (Y , A)}
        → Tmsᴹ p → Tmsᴹ (π₁ p)
    -- Term methods
    π₂ᴹ : {X Y : Con} {A : Ty n Y} {p : Tms X (Y , A)}
        → Tmsᴹ p → Tmᴹ (π₂ p)
    _[_]ᴹ : {X Y : Con} {A : Ty n Y} {u : Tm n Y A} {p : Tms X Y}
          → Tmᴹ u → Tmsᴹ p → Tmᴹ (u [ p ])
    lamᴹ : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {u : Tm n (X , A) B}
         → Tmᴹ u → Tmᴹ (lam u)
    appᴹ : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {u : Tm n X (Pi A B)}
         → Tmᴹ u → Tmᴹ (app u)

    isPropTmsᴹ : {X Y : Con} {p : Tms X Y} → isProp (Tmsᴹ p)
    isPropTmᴹ : {n : ℕ} {X : Con} {A : Ty n X} {u : Tm n X A} → isProp (Tmᴹ u)
    isPropTyᴹ : {n : ℕ} {X : Con} {A : Ty n X} → isProp (Tyᴹ A)

  {- Just like the definition of terms, the eliminator function is made 
     non mutually inductive to avoid some mutual dependency problems.
  -}
  termᴹ : {i : term-index} (u : term i) → term-motive u

  postulate
    tm→tm : {n : ℕ} {X : Con} {A B : Ty n X} {u : Tm n X A}
            → (f : {i : term-index} (u : term i) → term-motive u)
            → (p : A ≡ B)
            → Tmᴹ u [ i1 ↦ (λ _ → f u) ]
            → Tmᴹ (subst (Tm n X) p u) [ i1 ↦ (λ _ → f (subst (Tm n X) p u)) ]
    anything : ∀{l} {x : Set l} → x
--  tm→tm {n} {X} {u = u} p m = {!!} --transport (λ i → Tmᴹ (subst-fill (Tm n X) p u i)) m

  termᴹ (A [ p ]T) = (termᴹ A) [ termᴹ p ]Tᴹ
  termᴹ (U n) = Uᴹ
  termᴹ (El u) = Elᴹ (termᴹ u)
  termᴹ (Pi A B) = Piᴹ (termᴹ A) (termᴹ B)
  --termᴹ (L A) = Lᴹ (termᴹ A)
  termᴹ idt = idtᴹ
  termᴹ (p ∘t v) = termᴹ p ∘tᴹ termᴹ v
  termᴹ ε = εᴹ
  termᴹ (p , u) = termᴹ p ,ᴹ termᴹ u
  termᴹ (π₁ p) = π₁ᴹ (termᴹ p)
  termᴹ (π₂ p) = π₂ᴹ (termᴹ p)
  termᴹ (u [ p ]) = termᴹ u [ termᴹ p ]ᴹ
  termᴹ (lam u) = lamᴹ (termᴹ u)
  termᴹ (app u) = appᴹ (termᴹ u)
  termᴹ ([id]T {A = A} i) = isPropPath {B = λ i → Tyᴹ ([id]T i)} isPropTyᴹ (termᴹ A [ idtᴹ ]Tᴹ) (termᴹ A) i
  termᴹ ([∘]T {A = A} {p = p} {v = v} i) = isPropPath {B = λ i → Tyᴹ ([∘]T i)} isPropTyᴹ
                                                      (termᴹ A [ termᴹ p ∘tᴹ termᴹ v ]Tᴹ)
                                                      (termᴹ A [ termᴹ p ]Tᴹ [ termᴹ v ]Tᴹ) i
  termᴹ (U[] {p = p} i) = isPropPath {B = λ i → Tyᴹ (U[] i)} isPropTyᴹ
                                     (Uᴹ [ termᴹ p ]Tᴹ)
                                     Uᴹ i
  termᴹ (ʻEl[] {u = u} {p = p} {z} P i) = isPropPath {B = λ i → Tyᴹ (ʻEl[] P i)} isPropTyᴹ
                                                     (Elᴹ (termᴹ u) [ termᴹ p ]Tᴹ)
                                                     (Elᴹ (termᴹ z))
                                                     i
  termᴹ (ʻPi[] {X = X} {Y} {A} {B} {p} {z} P i) = isPropPath {B = λ i → Tyᴹ (ʻPi[] P i)} isPropTyᴹ
                                                      (Piᴹ (termᴹ A) (termᴹ B) [ termᴹ p ]Tᴹ)
                                                      (Piᴹ (termᴹ A [ termᴹ p ]Tᴹ) (termᴹ B [ (termᴹ p ∘tᴹ π₁ᴹ idtᴹ) ,ᴹ termᴹ z ]Tᴹ)) i
  --termᴹ (L[] {A = A} {p = p} i) = isPropPath {B = λ i → Tyᴹ (L[] i)} isPropTyᴹ
  --                            (Lᴹ (termᴹ A) [ termᴹ p ]Tᴹ)
  --                            (Lᴹ (termᴹ A [ termᴹ p ]Tᴹ)) i
  termᴹ (id∘ {p = p} i) = isPropPath {B = λ i → Tmsᴹ (id∘ i)} isPropTmsᴹ (idtᴹ ∘tᴹ termᴹ p) (termᴹ p) i
  termᴹ (∘id {p = p} i) = isPropPath {B = λ i → Tmsᴹ (∘id i)} isPropTmsᴹ (termᴹ p ∘tᴹ idtᴹ) (termᴹ p) i
  termᴹ (∘∘ {p = p} {v = v} {q = q} i) = isPropPath {B = λ i → Tmsᴹ (∘∘ i)} isPropTmsᴹ ((termᴹ p ∘tᴹ termᴹ v) ∘tᴹ termᴹ q) (termᴹ p ∘tᴹ (termᴹ v ∘tᴹ termᴹ q)) i
  termᴹ (εη {p = p} i) = isPropPath {B = λ i → Tmsᴹ (εη i)} isPropTmsᴹ (termᴹ p) (termᴹ ε) i
  termᴹ (π₁β {p = p} {u = u} i) = isPropPath {B = λ i → Tmsᴹ (π₁β i)} isPropTmsᴹ (π₁ᴹ (termᴹ p ,ᴹ termᴹ u)) (termᴹ p) i
  termᴹ (πη {p = p} i) = isPropPath {B = λ i → Tmsᴹ (πη i)} isPropTmsᴹ (π₁ᴹ (termᴹ  p) ,ᴹ π₂ᴹ (termᴹ p)) (termᴹ p) i
  termᴹ (ʻ,∘ {p = p} {v = v} {u = u} {z = z} P i) = isPropPath {B = λ i → Tmsᴹ (ʻ,∘ P i)} isPropTmsᴹ
                                                              ((termᴹ p ,ᴹ termᴹ u) ∘tᴹ termᴹ v)
                                                              ((termᴹ p ∘tᴹ termᴹ v) ,ᴹ termᴹ z) i
  termᴹ (ʻπ₂β {p = p} {u = u} {z = z} uz i) = isPropPath {B = λ i → Tmᴹ (ʻπ₂β uz i)} isPropTmᴹ
                                                         (π₂ᴹ (termᴹ p ,ᴹ termᴹ u ))
                                                         (termᴹ z)
                                                         i
  termᴹ (β {u = u} i) = isPropPath {B = λ i → Tmᴹ (β i)} isPropTmᴹ (appᴹ (lamᴹ (termᴹ u))) (termᴹ u) i
  termᴹ (η {f = f} i) = isPropPath {B = λ i → Tmᴹ (η i)} isPropTmᴹ (lamᴹ (appᴹ (termᴹ f))) (termᴹ f) i
  termᴹ (ʻlam[] {u = u} {p = p} {z = z} P Q i) = isPropPath {B = λ i → Tmᴹ (ʻlam[] P Q i)} isPropTmᴹ
                                                    (lamᴹ (termᴹ u) [ termᴹ p ]ᴹ)
                                                    (termᴹ z)
                                                    i
  termᴹ (isSetTy x y x≡y₁ x≡y₂ i j) = isPropPath* {B = λ i j → term-motive (isSetTy x y x≡y₁ x≡y₂ i j)} isPropTyᴹ
                                                  (λ i → termᴹ x)
                                                  (λ i → termᴹ y)
                                                  (λ i → termᴹ (x≡y₁ i))
                                                  (λ i → termᴹ (x≡y₂ i))
                                                  i j
  termᴹ (isSetTm x y x≡y₁ x≡y₂ i j) = isPropPath* {B = λ i j → term-motive (isSetTm x y x≡y₁ x≡y₂ i j)} isPropTmᴹ
                                                  (λ i → termᴹ x)
                                                  (λ i → termᴹ y)
                                                  (λ i → termᴹ (x≡y₁ i))
                                                  (λ i → termᴹ (x≡y₂ i))
                                                  i j
  termᴹ (isSetTms x y x≡y₁ x≡y₂ i j) = isPropPath* {B = λ i j → term-motive (isSetTms x y x≡y₁ x≡y₂ i j)} isPropTmsᴹ
                                                   (λ i → termᴹ x)
                                                   (λ i → termᴹ y)
                                                   (λ i → termᴹ (x≡y₁ i))
                                                   (λ i → termᴹ (x≡y₂ i))
                                                   i j
  termᴹ (El-injective {x = x} {y = y} x≡y i) = isPropPath {B = λ i → Tmᴹ (El-injective x≡y i)} isPropTmᴹ (termᴹ x) (termᴹ y) i

  -- And the nicer looking version of the previous function.
  elimTm : {X : Con} {A : Ty n X} (u : Tm n X A) → Tmᴹ u
  elimTm u = termᴹ u

  elimTms : {X Y : Con} (p : Tms X Y) → Tmsᴹ p
  elimTms p = termᴹ p

  elimTy : {X : Con} (A : Ty n X) → Tyᴹ A
  elimTy A = termᴹ A
