{-# OPTIONS --cubical --allow-unsolved-metas #-}
module TermInfo where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas

private variable n : ℕ

domains : {X : Con} → Ty n X → Maybe (Σ[ A ∈ Ty n X ] Ty n (X , A))
domains (A [ p ]T) with domains A
... | nothing = nothing
... | just (dom , cod) = just (dom [ p ]T , cod [ p ↑ dom ]T)
domains (U n) = nothing
domains (El x) = nothing
domains (Pi A B) = just (A , B)
--domains (L x) = nothing
domains ([id]T {X = X} {A = A} i) = P i
  where P : domains (A [ idt ]T) ≡ domains A
        P with domains A
        ... | nothing = refl
        ... | just (dom , cod) = λ i → just ([id]T {A = dom} i , hcollapse Q (cong (X Con.,_) ([id]T {A = dom})) i)
          where Q : cod [ idt ↑ dom ]T ⟦ Ty _ ⟧ cod
                Q = cod [ idt ↑ dom ]T
                    ⟮ hcong (cod [_]T) ↑id ⟯
                    cod [ idt ]T
                    ⟮ ‼ [id]T ⟯
                    cod □
domains ([∘]T {X = X} {A = A} {p} {v} i) = P i
  where P : domains (A [ p ∘t v ]T) ≡ domains (A [ p ]T [ v ]T)
        P with domains A
        ... | nothing = refl
        ... | just (dom , cod) = λ i → just ([∘]T {A = dom} i , hcollapse Q (cong (X Con.,_) ([∘]T {A = dom})) i)
          where Q : cod [ (p ∘t v) ↑ dom ]T ⟦ Ty _ ⟧ cod [ p ↑ dom ]T [ v ↑ (dom [ p ]T) ]T
                Q = cod [ (p ∘t v) ↑ dom ]T
                    ⟮ hcong (cod [_]T) (hsym ↑∘↑) ⟯
                    (cod [ (p ↑ dom) ∘t (v ↑ (dom [ p ]T)) ]T)
                    ⟮ ‼ [∘]T ⟯
                    ((cod [ p ↑ dom ]T) [ v ↑ (dom [ p ]T) ]T) □
domains (U[] i) = nothing
domains (ʻEl[] P i) = nothing
domains (ʻPi[] {n} {X = X} {Y = Y} {A = A} {B} {p} P i) = just ((A [ p ]T) , (B [ (p ∘t π₁ idt)
                                                           , transp (λ j → Tm n (X , (A [ p ]T))
                                                                    (sym ([∘]T {Y = X} {Z = Y} {A = A} {p = p} {v = π₁ idt}) (j ∨ i))) i (P i) ]T))
--domains (ʻL[] P i) = nothing
domains (isSetTy x y p q i j)
  = isSetMaybe (isSetΣ isSetTy isSetTy) _ _ (λ k → domains (p k)) (λ k → domains (q k)) i j

U≢El : {X : Con} {u : Tm (suc (suc n)) X (U (suc n))} → U n ≡ El u → ⊥
U≢El p = true≢false (cong P p)
  where P : {n : ℕ} {X : Con} → Ty n X → Bool
        P (x [ x₁ ]T) = P x
        P (U n) = true
        P (El x) = false
        P (Pi A x) = false
        P ([id]T {A = A} i) = P A
        P ([∘]T {A = A} i) = P A
        P (U[] i) = true
        P (ʻEl[] x i) = false
        P (ʻPi[] x i) = false
        P (isSetTy x y p q i j) = isSetBool (P x) (P y) (cong P p) (cong P q) i j

U≢Pi : {X : Con} {A : Ty (suc n) X} {B : Ty (suc n) (X , A)} → U n ≡ Pi A B → ⊥
U≢Pi p = true≢false (cong P p)
  where P : {n : ℕ} {X : Con} → Ty n X → Bool
        P (x [ x₁ ]T) = P x
        P (U n) = true
        P (El x) = false
        P (Pi A x) = false
        P ([id]T {A = A} i) = P A
        P ([∘]T {A = A} i) = P A
        P (U[] i) = true
        P (ʻEl[] x i) = false
        P (ʻPi[] x i) = false
        P (isSetTy x y p q i j) = isSetBool (P x) (P y) (cong P p) (cong P q) i j

El≢Pi : {X : Con} {u : Tm (suc n) X (U n)} {A : Ty n X} {B : Ty n (X , A)} → El u ≡ Pi A B → ⊥
El≢Pi p = true≢false (cong P p)
  where P : {n : ℕ} {X : Con} → Ty n X → Bool
        P (x [ x₁ ]T) = P x
        P (U n) = false
        P (El x) = true
        P (Pi A x) = false
        P ([id]T {A = A} i) = P A
        P ([∘]T {A = A} i) = P A
        P (U[] i) = false
        P (ʻEl[] x i) = true
        P (ʻPi[] x i) = false
        P (isSetTy x y p q i j) = isSetBool (P x) (P y) (cong P p) (cong P q) i j

{--
El-injective : {X : Con} {x y : Tm (suc n) X (U n)} → El x ≡ El y → x ≡ y
El-injective {n} {X} {x} x≡y i = El-elim (x≡y i) (λ j → x≡y (i ∧ j))
  where El-elim : (z : Ty n X) → El x ≡ z → Tm (suc n) X (U n)
        El-elim (x [ s ]T) p = {!(El-elim x) [ s ] !}
        El-elim (U n) p = absurd (U≢El (sym p))
        El-elim (El x) p = x
        El-elim (Pi A x) p = absurd (El≢Pi p)
        El-elim ([id]T i) p = {!!}
        El-elim ([∘]T i) p = {!!}
        El-elim (U[] i) p = {!!}
        El-elim (ʻEl[] x i) p = {!!}
        El-elim (ʻPi[] x i) p = {!!}
        El-elim (isSetTy x y p q i j) xz = {!!} --}
