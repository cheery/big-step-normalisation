{-# OPTIONS --cubical #-}
module SCVA where

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
--open import EvaluatorSC

private variable n : ℕ

-- Implements a well-founded relation around substitutions
TyS-domains : {X : Con} → TyS n X → Maybe (Σ[ A ∈ TyS n X ] TyS n (X , ⌜ A ⌝TyS))
TyS-domains (U n) = nothing
TyS-domains (El x) = nothing
TyS-domains (Pi A B) = just (A , B)

data TmsRel : {X Y : Con} → TyS n X → Tms X Y → TyS n Y → Set where
  Pi0 : {X Y : Con} {A : TyS n X} {B : TyS n Y} {C : TyS n (Y , ⌜ B ⌝TyS)} {p : Tms X Y}
     → A ≡ B [ p ]TyS
     → TmsRel A p (Pi B C)
  Pi1 : {X Y : Con} {A : TyS n X} {B : TyS n Y} {C : TyS n (Y , ⌜ B ⌝TyS)} {p : Tms X (Y , ⌜ B ⌝TyS)}
     → A ≡ C [ p ]TyS
     → TmsRel A (π₁ p) (Pi B C)

data TmsAcc {Y : Con} (A : TyS n Y) : Set where
  tmsacc : (∀ {X} (B : TyS n X) (p : Tms X Y) → TmsRel B p A → TmsAcc B) → TmsAcc A

_[_]TmsAcc : {X Y : Con} {A : TyS n Y} → TmsAcc A → (p : Tms X Y) → TmsAcc (A [ p ]TyS)
_[_]TmsAcc {.(suc n)} {X} {Y} {U n} (tmsacc f) p = tmsacc λ B s ()
_[_]TmsAcc {n} {X} {Y} {El x} (tmsacc f) p = tmsacc λ B s ()
_[_]TmsAcc {n} {X} {Y} {Pi A B} (tmsacc f) p = tmsacc λ B s rel → rel-wk B s rel refl
  where rel-wk : {Z : Con} (C : TyS n Z) (s : Tms Z X) {D : TyS n X} → TmsRel C s D → D ≡ (Pi (A [ p ]TyS) (subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS))) → TmsAcc C
        rel-wk B s (Pi0 x) z = subst TmsAcc (sym (x ∙ cong (_[ s ]TyS) P)) (f (A [ p ]TyS [ s ]TyS) (p ∘t s) (Pi0 (sym TyS[∘])))
          where P = cong fst (just-injective (cong TyS-domains z))
        rel-wk {Z} B' .(π₁ _) (Pi1 {B = D} {C = C} {p = s} x) z = subst TmsAcc (sym (hmerge Q)) (f goal (π₁ goal') (Pi1 (sym TyS[∘])) )
          where P = cong snd (just-injective (cong TyS-domains z))
                L = cong fst (just-injective (cong TyS-domains z))
                T : ⌜ D ⌝TyS ⟦ Ty _ ⟧ ⌜ A ⌝TyS [ p ]T
                T = ⌜ D ⌝TyS
                    ⟮ ‼ cong ⌜_⌝TyS L ⟯
                    ⌜ A [ p ]TyS ⌝TyS
                    ⟮ ‼ ⌜[]TyS⌝ ⟯
                    ⌜ A ⌝TyS [ p ]T □
                R : C ⟦ TyS _ ⟧ B [ p ↑ ⌜ A ⌝TyS ]TyS
                R = C
                    ⟮ ‼ P ⟯
                    subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)
                    ⟮ ‼ sym (subst-fill (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)) ⟯
                    B [ p ↑ ⌜ A ⌝TyS ]TyS □
                goal = B [ p ↑ ⌜ A ⌝TyS ]TyS [ subst (λ i → Tms Z (X , i)) (hmerge T) s ]TyS
                goal' = (p ↑ ⌜ A ⌝TyS) ∘t subst (λ i → Tms Z (X , i)) (hmerge T) s
                Q : B' ⟦ TyS _ ⟧ goal
                Q = B'
                    ⟮ ‼ x ⟯
                    C [ s ]TyS
                    ⟮ ‼ dcong₂ (_[_]TyS) (hcollapse R (cong (X Con.,_) (hmerge T))) (subst-filler (λ i → Tms Z (X , i)) (hmerge T) s) ⟯
                    goal □

tmswf : {Y : Con} (A : TyS n Y) → TmsAcc A
tmswf-aux : {Y : Con} {A : TyS n Y} {X : Con} (B : TyS n X) (p : Tms X Y) → TmsRel B p A → TmsAcc B

tmswf {n} {Y} A = tmsacc tmswf-aux

tmswf-aux B p (Pi0 {B = C} x) = subst TmsAcc (sym x) (tmswf C [ p ]TmsAcc)
tmswf-aux B .(π₁ _) (Pi1 {C = C} {p = p} x) = subst TmsAcc (sym x) (tmswf C [ p ]TmsAcc)

blank-transp : ∀{l} {A : Set l} → I → A → A
blank-transp {A = A} i x = transp (λ _ → A) i x

isPropTmsAcc : {Y : Con} {A : TyS n Y} → isProp (TmsAcc A)
isPropTmsAcc {n} {Y} {A} (tmsacc f) (tmsacc g) i = tmsacc λ B p rel → isPropTmsAcc (f B p rel) (g B p rel) i

TySAcc≡TyS : {X : Con} → (Σ[ A ∈ TyS n X ] (TmsAcc A)) ≡ TyS n X
TySAcc≡TyS {n} {X} = sym (isoToPath (iso (λ tys → tys , tmswf tys) (λ (tys , acc) → tys) (λ (B , acc) i → B , isPropTmsAcc (tmswf B) acc i) λ A → refl))

TySAcc≡Ty : {X : Con} → Σ (TyS n X) TmsAcc ≡ (Ty n X)
TySAcc≡Ty = isoToPath (iso (λ (tys , acc) → ⌜ tys ⌝TyS)
                           (λ ty → let tys = fst (evalT* ty) in tys , tmswf tys)
                           (λ ty → sym (evalT≡ (snd (evalT* ty))))
                           λ (tys , acc) → λ i → let t = sym (teq (evalT≡ (snd (evalT* ⌜ tys ⌝TyS))))
                                                   in t i , isPropPath {B = λ k → TmsAcc (t k)} isPropTmsAcc (tmswf (fst (evalT* ⌜ tys ⌝TyS))) acc i)

TySAcc≡Ty-Ty : {n : ℕ} {X : Con} → PathP (λ i → (TySAcc≡Ty {n} {X} i → Ty n X)) (λ A → ⌜ fst A ⌝TyS) (λ A → A)
TySAcc≡Ty-Ty {n} {X} i A = unglue (i ∨ ~ i) A

TySAcc≡Ty-TyS : {n : ℕ} {X : Con} → PathP (λ i → (TySAcc≡Ty {n} {X} i → TyS n X)) (λ A → fst A) (λ A → fst (evalT* A))
TySAcc≡Ty-TyS {n} {X} i = hcomp (λ k → λ{(i = i0) → λ A → teq (evalT≡ (snd (evalT* ⌜ fst A ⌝TyS))) (~ k)
                                         ;(i = i1) → λ A → fst (evalT* A)})
                                         (λ A → fst (evalT* (unglue (i ∨ ~ i) A)))

TySAcc≡Ty-TyS≡Ty : {n : ℕ} {X : Con} → PathP (λ i → (TySAcc≡Ty {n} {X} i → TyS≡Ty {n} {X} i)) (λ A → fst A) (λ A → A)
TySAcc≡Ty-TyS≡Ty {n} {X} i A = glue (λ{(i = i0) → TySAcc≡Ty-TyS i A ; (i = i1) → TySAcc≡Ty-Ty i A}) (unglue (i ∨ ~ i) A)

TySAcc≡Ty-mk : {n : ℕ} {X : Con} (A : TyS n X) (acc : TmsAcc A) → PathP (λ i → TySAcc≡Ty {n} {X} i) (A , acc) ⌜ A ⌝TyS
TySAcc≡Ty-mk {n} {X} A acc i = glue (λ{(i = i0) → A , acc; (i = i1) → ⌜ A ⌝TyS}) ⌜ A ⌝TyS

⌞_∶_⌟TyS≡Ty : {X : Con} → PathP (λ i → TyS≡Ty {n} {X} i → TyS n X) id (λ A → fst (evalT* A))
⌞_∶_⌟TyS≡Ty {n} {X} i = hcomp (λ k → λ{(i = i0) → λ A → teq (evalT≡ (snd (evalT* ⌜ A ⌝TyS))) (~ k)
                                       ;(i = i1) → λ A → fst (evalT* A)})
                                       (λ A → fst (evalT* (unglue (i ∨ ~ i) A)))

⌜_∶_⌝TyS≡Ty : {X : Con} → PathP (λ i → TyS≡Ty {n} {X} i → Ty n X) ⌜_⌝TyS id 
⌜_∶_⌝TyS≡Ty {n} {X} i A = unglue (i ∨ ~ i) A

TyS≡Ty-Pi : {X : Con} → PathP (λ i → (A : TyS≡Ty {n} {X} i) → TyS≡Ty {n} {X , ⌜ i ∶ A ⌝TyS≡Ty} i → TyS≡Ty {n} {X} i) Pi Pi
TyS≡Ty-Pi {n} {X} i A B = glue (λ{(i = i0) → Pi A B; (i = i1) → Pi A B}) (Pi (unglue (i ∨ ~ i) A) (unglue (i ∨ ~ i) B))

TySAcc≡Ty-mk₂ : {n : ℕ} {X : Con} → PathP (λ i → (A : TyS≡Ty {n} {X} i)
                                                 → (acc : TmsAcc ⌞ i ∶ A ⌟TyS≡Ty)
                                                 → TySAcc≡Ty {n} {X} i) (λ A acc → (A , acc)) (λ A acc → A)
TySAcc≡Ty-mk₂ {n} {X} i A acc = glue (λ{(i = i0) → A , acc ;(i = i1) → A}) (unglue (i ∨ ~ i) A)

abstract
  _∶_[_]TyS≡Ty : {X Y : Con} → PathP (λ i → TyS≡Ty {n} {Y} i → Tms X Y → TyS≡Ty {n} {X} i) _[_]TyS _[_]T
  _∶_[_]TyS≡Ty {n} {X} {Y} i = hcomp (λ k → λ{(i = i0) → λ A p → teq (evalT≡ (snd (evalT* ⌜ A ⌝TyS))) (~ k) [ p ]TyS
                                            ;(i = i1) → λ A p → Q A p k})
                                             (λ A p → glue (λ{(i = i0) → (fst (evalT* ⌜ A ⌝TyS)) [ p ]TyS
                                                              ;(i = i1) → ⌜ fst (evalT* A) [ p ]TyS ⌝TyS})
                                                              ⌜ fst (evalT* (unglue (i ∨ ~ i) A)) [ p ]TyS ⌝TyS)
    where Q : (A : Ty n Y) (p : Tms X Y) → ⌜ fst (evalT* A) [ p ]TyS ⌝TyS ≡ A [ p ]T
          Q A p = ⌜[]TyS⌝ ∙ cong (_[ p ]T) (sym (evalT≡ (snd (evalT* A))))

isSetTySAcc : {X : Con} → isSet (Σ (TyS n X) TmsAcc)
isSetTySAcc {n} {X} = transport (λ i → isSet (TySAcc≡Ty {n} {X} (~ i))) isSetTy

{--_[_]TySAcc* : {X Y : Con} → Σ (TyS n Y) TmsAcc → Tms X Y → Σ (TyS n X) TmsAcc
_[_]TySAcc* {n} {X} {Y} = transport (λ i → TySAcc≡Ty {n} {Y} (~ i) → Tms X Y → TySAcc≡Ty {n} {X} (~ i)) _[_]T

_∶_[_]TySAcc*≡Ty : {X Y : Con} → PathP (λ i → TySAcc≡Ty {n} {Y} i → Tms X Y → TySAcc≡Ty {n} {X} i) _[_]TySAcc* _[_]T
_∶_[_]TySAcc*≡Ty {n} {X} {Y} i = transport-filler (λ i → TySAcc≡Ty {n} {Y} (~ i) → Tms X Y → TySAcc≡Ty {n} {X} (~ i)) _[_]T (~ i)
--}

_[_]TySAcc : {X Y : Con} → Σ (TyS n Y) TmsAcc → Tms X Y → Σ (TyS n X) TmsAcc
_[_]TySAcc (tys , acc) p = tys [ p ]TyS , (acc [ p ]TmsAcc)

_∶_[_]TySAcc≡Ty : {X Y : Con} → PathP (λ i → TySAcc≡Ty {n} {Y} i → Tms X Y → TySAcc≡Ty {n} {X} i) _[_]TySAcc _[_]T
_∶_[_]TySAcc≡Ty {n} {X} {Y} i = hcomp (λ k → λ{(i = i0) → λ A p → P A p k , isPropPath (λ{i} → isPropTmsAcc {A = P A p i}) (tmswf (fst (evalT* ⌜ fst A ⌝TyS)) [ p ]TmsAcc)
                                                                                                                               (snd A [ p ]TmsAcc) k
                                               ;(i = i1) → λ A p → Q A p k})
                                               λ A p → glue (λ{(i = i0) → fst (evalT* ⌜ fst A ⌝TyS) [ p ]TyS , (tmswf (fst (evalT* ⌜ fst A ⌝TyS)) [ p ]TmsAcc)
                                                               ;(i = i1) → ⌜ fst (evalT* A) [ p ]TyS ⌝TyS})
                                                               ⌜ fst (evalT* (unglue (i ∨ ~ i) A)) [ p ]TyS ⌝TyS
  where P : (A : Σ (TyS n Y) TmsAcc) (p : Tms X Y) → fst (evalT* ⌜ fst A ⌝TyS) [ p ]TyS ≡ fst A [ p ]TyS
        P A p = cong (_[ p ]TyS) (sym (teq (evalT≡ (snd (evalT* ⌜ fst A ⌝TyS))))) 
        Q : (A : Ty n Y) (p : Tms X Y) → ⌜ fst (evalT* A) [ p ]TyS ⌝TyS ≡ A [ p ]T
        Q A p = ⌜[]TyS⌝ ∙ cong (_[ p ]T) (sym (evalT≡ (snd (evalT* A))))

⌜_⌝TySAcc : {X : Con} (A : Σ (TyS n X) TmsAcc) → Ty n X
⌜ A ⌝TySAcc = ⌜ fst A ⌝TyS

⌜[]TySAcc⌝ : {X Y : Con} {A : Σ (TyS n Y) TmsAcc} {s : Tms X Y}
       → ⌜ A [ s ]TySAcc ⌝TySAcc ≡ ⌜ A ⌝TySAcc [ s ]T
⌜[]TySAcc⌝ {n} {X} {Y} {A} {s} = transport (λ i → {A : TySAcc≡Ty {n} {Y} (~ i)} {s : Tms X Y} → TySAcc≡Ty-Ty (~ i) ((~ i) ∶ A [ s ]TySAcc≡Ty) ≡ (TySAcc≡Ty-Ty (~ i) A) [ s ]T) refl {A} {s}

⌜[]TySAcc≡Ty⌝ : {X Y : Con} → (PathP (λ i → (A : TySAcc≡Ty {n} {Y} i) (s : Tms X Y) → TySAcc≡Ty-Ty i (i ∶ A [ s ]TySAcc≡Ty) ≡ (TySAcc≡Ty-Ty i A) [ s ]T))
                                     (λ A s → ⌜[]TySAcc⌝ {A = A} {s = s})
                                     λ A s → refl
⌜[]TySAcc≡Ty⌝ {n} {X} {Y} i = transport-filler (λ i → (A : TySAcc≡Ty {n} {Y} (~ i)) (s : Tms X Y) → TySAcc≡Ty-Ty (~ i) ((~ i) ∶ A [ s ]TySAcc≡Ty) ≡ (TySAcc≡Ty-Ty (~ i) A) [ s ]T) (λ A s → refl) (~ i)

subst⌜[]TySAcc≡Ty⌝ : {X Y : Con} → PathP (λ i → {A : TySAcc≡Ty {n} {Y} i} {p : Tms X Y} → Val n X (TySAcc≡Ty-Ty i (i ∶ A [ p ]TySAcc≡Ty)) → Val n X (TySAcc≡Ty-Ty i A [ p ]T))
                                          (λ {A} {p} → subst (Val n X) (⌜[]TySAcc⌝ {A = A} {s = p}))
                                          (λ {A} {p} → id)
subst⌜[]TySAcc≡Ty⌝ {n} {X} {Y} i {A} {p} v = transp (λ j → Val n X (⌜[]TySAcc≡Ty⌝ {n} {X} {Y} i A p j)) i v

⌜[]TyS⌝* : {X Y : Con} {A : TyS n Y} {s : Tms X Y}
       → ⌜ A [ s ]TyS ⌝TyS ≡ ⌜ A ⌝TyS [ s ]T
⌜[]TyS⌝* {n} {X} {Y} {A} {s} = transport (λ i → {A : TyS≡Ty {n} {Y} (~ i)} {s : Tms X Y} → ⌜ (~ i) ∶ ((~ i) ∶ A [ s ]TyS≡Ty) ⌝TyS≡Ty ≡ (⌜ (~ i) ∶ A ⌝TyS≡Ty) [ s ]T) refl {A} {s}

⌜[]TyS≡Ty⌝ : {X Y : Con} → (PathP (λ i → (A : TyS≡Ty {n} {Y} i) (s : Tms X Y) → ⌜ i ∶ (i ∶ A [ s ]TyS≡Ty) ⌝TyS≡Ty ≡ (⌜ i ∶ A ⌝TyS≡Ty) [ s ]T))
                                     (λ A s → ⌜[]TyS⌝* {A = A} {s = s})
                                     λ A s → refl
⌜[]TyS≡Ty⌝ {n} {X} {Y} i A s = transport-filler (λ i → {A : TyS≡Ty {n} {Y} (~ i)} {s : Tms X Y} → ⌜ (~ i) ∶ ((~ i) ∶ A [ s ]TyS≡Ty) ⌝TyS≡Ty ≡ (⌜ (~ i) ∶ A ⌝TyS≡Ty) [ s ]T) (λ {A} {s} → refl) (~ i) {A} {s}

subst⌜[]TyS≡Ty⌝ : {X Y : Con} → PathP (λ i → {A : TyS≡Ty {n} {Y} i} {p : Tms X Y} → Val n X (⌜ i ∶ (i ∶ A [ p ]TyS≡Ty) ⌝TyS≡Ty) → Val n X (⌜ i ∶ A ⌝TyS≡Ty [ p ]T))
                                          (λ {A} {p} → subst (Val n X) (⌜[]TyS⌝* {A = A} {s = p}))
                                          (λ {A} {p} → id)
subst⌜[]TyS≡Ty⌝ {n} {X} {Y} i {A} {p} v = transp (λ j → Val n X (⌜[]TyS≡Ty⌝ {n} {X} {Y} i A p j)) i v


-- The new SCV-structure
scvB : {n : ℕ} {X : Con} → (A : TyS n X) → TmsAcc A → Val n X ⌜ A ⌝TyS → Set
scvB {X = X} (U n) acc v = Σ[ w ∈ Nf _ X (U n) ] quot v w
scvB {X = X} (El u) acc v = Σ[ w ∈ Nf _ X (El u) ] quot v w
scvB {n} {X = X} (Pi A B) (tmsacc acc) f = let
                          A' : {Y : Con} (a : Wk Y X) → TyS n Y
                          A' a = A [ ⌜ a ⌝Wk ]TyS
                          accA' : {Y : Con} (a : Wk Y X) → TmsAcc (A' a)
                          accA' a = (acc (A [ ⌜ a ⌝Wk ]TyS) ⌜ a ⌝Wk (Pi0 refl))
                          B' : {Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ (A' a , accA' a) ⌝TySAcc)) → TyS n Y
                          B' a v = B [ ⌜ a ⌝Wk , ⌜ subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) v ⌝Val ]TyS
                          accB' : {Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ (A' a , accA' a) ⌝TySAcc)) → TmsAcc (B' a v)
                          accB' a v = acc (B' a v) _ (Pi1 refl)
                          in {Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ (A' a , accA' a) ⌝TySAcc)) → scvB (A' a) (accA' a) v
                            → Σ[ w ∈ Val _ Y ⌜ B' a v , accB' a v ⌝TySAcc ]
                               (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst (Val _ _) (⌜[]TySAcc⌝ {A = A , tmswf A}) v) w × scvB (B' a v) (accB' a v) w)

scvA : {n : ℕ} {X : Con} → (A' : Σ[ A ∈ TyS n X ] TmsAcc A) → Val n X ⌜ fst A' ⌝TyS → Set
scvA (A , acc) v = scvB A acc v

scvA-access-U : {n : ℕ} {X : Con} → (v : Val (suc n) X ⌜ U n ⌝TyS) → scvA (U n , tmswf (U n)) v → Σ[ w ∈ Nf _ X (U n) ] quot v w
scvA-access-U v scv = scv

scvA-mk-U : {n : ℕ} {X : Con} → (v : Val (suc n) X ⌜ U n ⌝TyS) → Σ[ w ∈ Nf _ X (U n) ] quot v w → scvA (U n , tmswf (U n)) v
scvA-mk-U v scv = scv

scvA-access-El : {n : ℕ} {X : Con} {u : Tm (suc n) X (U n)} (v : Val n X ⌜ El u ⌝TyS) → scvA (El u , tmswf (El u)) v → Σ[ w ∈ Nf _ X (El u) ] quot v w
scvA-access-El v scv = scv

scvA-mk-El : {n : ℕ} {X : Con} {u : Tm (suc n) X (U n)} (v : Val n X ⌜ El u ⌝TyS) → Σ[ w ∈ Nf _ X (El u) ] quot v w → scvA (El u , tmswf (El u)) v
scvA-mk-El v scv = scv

{--
scvA-access-Pi : {n : ℕ} {X : Con} {A : TyS n X} {B : TyS n (X , ⌜ A ⌝TyS)}
                (f : Val n X ⌜ Pi A B ⌝TyS)
                → scvA (Pi A B , tmswf (Pi A B)) f
                → {Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ A [ ⌜ a ⌝Wk ]TyS ⌝TyS)) → scvA (_ , blank-transp i0 (tmswf A [ ⌜ a ⌝Wk ]TmsAcc)) v
                            → Σ[ w ∈ Val _ Y ⌜ B [ ⌜ a ⌝Wk , ⌜ subst (Val _ _) ⌜[]TyS⌝* v ⌝Val ]TyS ⌝TyS ]
                               (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst (Val _ _) ⌜[]TyS⌝* v) w × scvA (_ , blank-transp i0 (tmswf B [ _ ]TmsAcc)) w)
scvA-access-Pi f scv = scv

scvA-mk-Pi : {n : ℕ} {X : Con} {A : TyS n X} {B : TyS n (X , ⌜ A ⌝TyS)}
                (f : Val n X ⌜ Pi A B ⌝TyS)
                → ({Y : Con} (a : Wk Y X) (v : Val _ Y (⌜ A [ ⌜ a ⌝Wk ]TyS ⌝TyS)) → scvA (_ , blank-transp i0 (tmswf A [ ⌜ a ⌝Wk ]TmsAcc)) v
                            → Σ[ w ∈ Val _ Y ⌜ B [ ⌜ a ⌝Wk , ⌜ subst (Val _ _) ⌜[]TyS⌝* v ⌝Val ]TyS ⌝TyS ]
                               (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst (Val _ _) ⌜[]TyS⌝* v) w × scvA (_ , blank-transp i0 (tmswf B [ _ ]TmsAcc)) w))
                → scvA (Pi A B , tmswf (Pi A B)) f
scvA-mk-Pi f scv = scv --}

abstract
  scv : {n : ℕ} {X : Con} (A : Ty n X) → Val n X A → Set
  scv = transport (λ i → {n : ℕ} {X : Con} → (p : TySAcc≡Ty {n} {X} i) → Val n X (TySAcc≡Ty-Ty i p) → Set) scvA

  scvA≡scv : PathP (λ i → {n : ℕ} {X : Con} (p : TySAcc≡Ty {n} {X} i) → Val n X (TySAcc≡Ty-Ty i p) → Set) scvA scv
  scvA≡scv i = transport-filler (λ i → {n : ℕ} {X : Con} → (p : TySAcc≡Ty {n} {X} i) → Val n X (TySAcc≡Ty-Ty i p) → Set) scvA i

abstract
  scv-access-U : {n : ℕ} {X : Con} → (v : Val (suc n) X (U n)) → scv (U n) v → Σ[ w ∈ Nf _ X (U n) ] quot v w
  scv-access-U {n} {X} = transport (λ i → (v : Val (suc n) X (TySAcc≡Ty-Ty i (mkU i))) → scvA≡scv i (mkU i) v → Σ[ w ∈ Nf _ X (TySAcc≡Ty-Ty i (mkU i)) ] quot v w)
                                   (scvA-access-U {n} {X})
    where mkU : (i : I) → TySAcc≡Ty {suc n} {X} i
          mkU i = TySAcc≡Ty-mk (U n) (tmswf (U n)) i

  scv-mk-U : {n : ℕ} {X : Con} → (v : Val (suc n) X (U n)) → Σ[ w ∈ Nf _ X (U n) ] quot v w → scv (U n) v
  scv-mk-U {n} {X} = transport (λ i → (v : Val (suc n) X (TySAcc≡Ty-Ty i (mkU i))) → Σ[ w ∈ Nf _ X (TySAcc≡Ty-Ty i (mkU i)) ] quot v w → scvA≡scv i (mkU i) v)
                                   (scvA-mk-U {n} {X})
    where mkU : (i : I) → TySAcc≡Ty {suc n} {X} i
          mkU i = TySAcc≡Ty-mk (U n) (tmswf (U n)) i

  scv-access-El : {n : ℕ} {X : Con} {u : Tm (suc n) X (U n)} (v : Val n X (El u)) → scv (El u) v → Σ[ w ∈ Nf _ X (El u) ] quot v w
  scv-access-El {n} {X} {u} = transport (λ i → (v : Val n X (TySAcc≡Ty-Ty i (mkEl i))) → scvA≡scv i (mkEl i) v → Σ[ w ∈ Nf _ X (TySAcc≡Ty-Ty i (mkEl i)) ] quot v w)
                                   (scvA-access-El {n} {X})
    where mkEl : (i : I) → TySAcc≡Ty {n} {X} i
          mkEl i = TySAcc≡Ty-mk (El u) (tmswf (El u)) i

  scv-mk-El : {n : ℕ} {X : Con} {u : Tm (suc n) X (U n)} (v : Val n X (El u)) → Σ[ w ∈ Nf _ X (El u) ] quot v w → scv (El u) v
  scv-mk-El {n} {X} {u} = transport (λ i → (v : Val n X (TySAcc≡Ty-Ty i (mkEl i))) → Σ[ w ∈ Nf _ X (TySAcc≡Ty-Ty i (mkEl i)) ] quot v w → scvA≡scv i (mkEl i) v)
                                   (scvA-mk-El {n} {X})
    where mkEl : (i : I) → TySAcc≡Ty {n} {X} i
          mkEl i = TySAcc≡Ty-mk (El u) (tmswf (El u)) i


  blank-transp-TySAcc≡Ty : {X : Con} → PathP (λ i → TySAcc≡Ty {n} {X} i → TySAcc≡Ty {n} {X} i) (λ (A , acc) → (A , blank-transp i0 acc)) id
  blank-transp-TySAcc≡Ty {n} {X} i ty = glue (λ{(i = i0) → fst ty , blank-transp i0 (snd ty) ; (i = i1) → ty}) (unglue (i ∨ ~ i) ty)

  scv-access-Pi : {n : ℕ} {X : Con} {A : Ty n X} {B : Ty n (X , A)}
                  (f : Val n X (Pi A B))
                  → scv (Pi A B) f
                  → {Y : Con} (a : Wk Y X) (v : Val _ Y (A [ ⌜ a ⌝Wk ]T)) → scv (A [ ⌜ a ⌝Wk ]T) v
                              → Σ[ w ∈ Val _ Y (B [ ⌜ a ⌝Wk , ⌜ v ⌝Val ]T) ]
                                 (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) v) w × scv _ w
  scv-access-Pi {n} {X} {A} {B} = transport (λ i → {A : TyS≡Ty i} {B : TyS≡Ty i}
                                                    (f : Val n X (TySAcc≡Ty-Ty i (mkPi i A B))) → scvA≡scv i (mkPi i A B) f
                                                 → ({Y : Con} (a : Wk Y X)
                                                     (v : Val _ Y (TySAcc≡Ty-Ty i (A' i A a)))
                                                   → scvA≡scv i (A' i A a) v
                                                   → Σ[ w ∈ Val _ Y (TySAcc≡Ty-Ty i (C' i A B a v)) ]
                                                     (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst⌜[]TySAcc≡Ty⌝ i {A = TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty)} {p = ⌜ a ⌝Wk} v) w
                                                     × scvA≡scv i (C' i A B a v) w))) (λ v → id) {A} {B}
    where mkPi : (i : I) (A : TyS≡Ty {n} {X} i) (B : TyS≡Ty {n} {X , ⌜ i ∶ A ⌝TyS≡Ty} i) → TySAcc≡Ty {n} {X} i
          mkPi i A B = TySAcc≡Ty-mk₂ i (TyS≡Ty-Pi i A B) (tmswf ⌞ i ∶ TyS≡Ty-Pi i A B ⌟TyS≡Ty)
          A' : (i : I) (A : TyS≡Ty {n} {X} i) {Y : Con} (a : Wk Y X) → TySAcc≡Ty {n} {Y} i
          A' i A a = blank-transp-TySAcc≡Ty i
                     (i ∶ TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty) [ ⌜ a ⌝Wk ]TySAcc≡Ty)
          C' : (i : I) (A : TyS≡Ty {n} {X} i) (B : TyS≡Ty {n} {X , ⌜ i ∶ A ⌝TyS≡Ty} i) → {Y : Con} (a : Wk Y X)
            → (v : Val _ Y (TySAcc≡Ty-Ty i (A' i A a)))
            → TySAcc≡Ty {n} {Y} i
          C' i A B a v = blank-transp-TySAcc≡Ty i
                         (i ∶ TySAcc≡Ty-mk₂ i B (tmswf ⌞ i ∶ B ⌟TyS≡Ty) [ ⌜ a ⌝Wk , ⌜ subst⌜[]TySAcc≡Ty⌝ i {A = TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty)} {p = ⌜ a ⌝Wk} v ⌝Val ]TySAcc≡Ty)

  scv-mk-Pi : {n : ℕ} {X : Con} {A : Ty n X} {B : Ty n (X , A)}
                     (f : Val n X (Pi A B))
                  → ({Y : Con} (a : Wk Y X) (v : Val _ Y (A [ ⌜ a ⌝Wk ]T)) → scv (A [ ⌜ a ⌝Wk ]T) v
                                → Σ[ w ∈ Val _ Y (B [ ⌜ a ⌝Wk , ⌜ v ⌝Val ]T) ]
                                     (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) v) w × scv _ w)
                  → scv (Pi A B) f
  scv-mk-Pi {n} {X} {A} {B} = transport (λ i → {A : TyS≡Ty i} {B : TyS≡Ty i}
                                                    (f : Val n X (TySAcc≡Ty-Ty i (mkPi i A B)))
                                                 → ({Y : Con} (a : Wk Y X)
                                                     (v : Val _ Y (TySAcc≡Ty-Ty i (A' i A a)))
                                                   → scvA≡scv i (A' i A a) v
                                                   → Σ[ w ∈ Val _ Y (TySAcc≡Ty-Ty i (C' i A B a v)) ]
                                                     (apply (subst (Val _ Y) Pi[] (f [ a ]Val)) (subst⌜[]TySAcc≡Ty⌝ i {A = TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty)} {p = ⌜ a ⌝Wk} v) w
                                                     × scvA≡scv i (C' i A B a v) w))
                                                   → scvA≡scv i (mkPi i A B) f) (λ v → id) {A} {B}
    where mkPi : (i : I) (A : TyS≡Ty {n} {X} i) (B : TyS≡Ty {n} {X , ⌜ i ∶ A ⌝TyS≡Ty} i) → TySAcc≡Ty {n} {X} i
          mkPi i A B = TySAcc≡Ty-mk₂ i (TyS≡Ty-Pi i A B) (tmswf ⌞ i ∶ TyS≡Ty-Pi i A B ⌟TyS≡Ty)
          A' : (i : I) (A : TyS≡Ty {n} {X} i) {Y : Con} (a : Wk Y X) → TySAcc≡Ty {n} {Y} i
          A' i A a = blank-transp-TySAcc≡Ty i
                     (i ∶ TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty) [ ⌜ a ⌝Wk ]TySAcc≡Ty)
          C' : (i : I) (A : TyS≡Ty {n} {X} i) (B : TyS≡Ty {n} {X , ⌜ i ∶ A ⌝TyS≡Ty} i) → {Y : Con} (a : Wk Y X)
            → (v : Val _ Y (TySAcc≡Ty-Ty i (A' i A a)))
            → TySAcc≡Ty {n} {Y} i
          C' i A B a v = blank-transp-TySAcc≡Ty i
                         (i ∶ TySAcc≡Ty-mk₂ i B (tmswf ⌞ i ∶ B ⌟TyS≡Ty) [ ⌜ a ⌝Wk , ⌜ subst⌜[]TySAcc≡Ty⌝ i {A = TySAcc≡Ty-mk₂ i A (tmswf ⌞ i ∶ A ⌟TyS≡Ty)} {p = ⌜ a ⌝Wk} v ⌝Val ]TySAcc≡Ty)

sce : {X Y : Con} → Env X Y → Set
sce {Y = ∅} _ = ⊤
sce {Y = Y , A} (env (p , x)) = sce p × scv _ x
