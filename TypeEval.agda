{-# OPTIONS --cubical --allow-unsolved-metas #-}
module TypeEval where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
--open import Weakening
--open import Values
--open import NormalForm
open import TermInfo
--open import Stability

private variable n : ℕ

-- Substitution free types
data TyS : ℕ → Con → Set
⌜_⌝TyS : {X : Con} → TyS n X → Ty n X

data TyS where
  U : {X : Con} → (n : ℕ) → TyS (suc n) X
  El : {X : Con} → Tm (suc n) X (U n) → TyS n X
  --L : {X : Con} → TyS n X → TyS (suc n) X
  Pi : {X : Con} → (A : TyS n X) → (B : TyS n (X , ⌜ A ⌝TyS)) → TyS n X

⌜ U n ⌝TyS = U n
⌜ El x ⌝TyS = El x
--⌜ L A ⌝TyS = L ⌜ A ⌝TyS
⌜ Pi A B ⌝TyS = Pi ⌜ A ⌝TyS ⌜ B ⌝TyS

_[_]TyS : {X Y : Con} → TyS n Y → Tms X Y → TyS n X
⌜[]TyS⌝ : {X Y : Con} {A : TyS n Y} {s : Tms X Y}
       → ⌜ A [ s ]TyS ⌝TyS ≡ ⌜ A ⌝TyS [ s ]T

U n [ s ]TyS = U n
El x [ s ]TyS = El (subst (Tm _ _) U[] (x [ s ]))
--L A [ s ]TyS = L (A [ s ]TyS)
Pi A B [ s ]TyS = Pi (A [ s ]TyS) (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ s ↑ ⌜ A ⌝TyS ]TyS))

⌜[]TyS⌝ {X = X} {Y = Y} {A = U n} {s = s} = sym U[]
⌜[]TyS⌝ {X = X} {Y = Y} {A = El u} {s = s} = sym El[]
⌜[]TyS⌝ {X = X} {Y = Y} {A = Pi A B} {s = s} = hmerge P
    where P : Pi ⌜ A [ s ]TyS ⌝TyS ⌜ subst (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ s ↑ ⌜ A ⌝TyS ]TyS) ⌝TyS
              ⟦ Ty _ ⟧
              (Pi ⌜ A ⌝TyS ⌜ B ⌝TyS [ s ]T)
          P = Pi ⌜ A [ s ]TyS ⌝TyS ⌜ subst (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ s ↑ ⌜ A ⌝TyS ]TyS) ⌝TyS
              ⟮ ‼ dcong₂ (λ x y → term.Pi x ⌜ y ⌝TyS) ⌜[]TyS⌝ (sym (subst-filler (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ s ↑ ⌜ A ⌝TyS ]TyS))) ⟯
              Pi (⌜ A ⌝TyS [ s ]T) ⌜ B [ s ↑ ⌜ A ⌝TyS ]TyS ⌝TyS
              ⟮ ‼ cong (λ x → term.Pi (⌜ A ⌝TyS [ s ]T) x) ⌜[]TyS⌝ ⟯
              Pi (⌜ A ⌝TyS [ s ]T) (⌜ B ⌝TyS [ s ↑ ⌜ A ⌝TyS ]T)
              ⟮ ‼ sym Pi[] ⟯
              Pi ⌜ A ⌝TyS ⌜ B ⌝TyS [ s ]T □

abstract
  TyS[id] : {X : Con} {A : TyS n X} → A [ idt ]TyS ≡ A
  TyS[id] {X = X} {U n} = refl
  TyS[id] {X = X} {El u} = cong TyS.El (hmerge P)
    where P : (subst (Tm _ X) U[] (u [ idt ])) ⟦ Tm _ X ⟧ u
          P = (subst (Tm _ X) U[] (u [ idt ]))
              ⟮ ‼ sym (subst-filler (Tm _ X) U[] (u [ idt ])) ⟯
              u [ idt ]
              ⟮ [id] ⟯
              u □
  TyS[id] {X = X} {Pi A B} = cong₂ TyS.Pi TyS[id] (hcollapse Q (cong (λ i → (X Con., ⌜ i ⌝TyS)) TyS[id]))
    where Q : subst (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ idt ↑ ⌜ A ⌝TyS ]TyS) ⟦ TyS _ ⟧ B
          Q = subst (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ idt ↑ ⌜ A ⌝TyS ]TyS)
              ⟮ ‼ sym (subst-filler (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝) (B [ idt ↑ ⌜ A ⌝TyS ]TyS)) ⟯
              B [ idt ↑ ⌜ A ⌝TyS ]TyS
              ⟮ hcong (B [_]TyS) ↑id ⟯
              B [ idt ]TyS
              ⟮ ‼ TyS[id] ⟯
              B □

  TyS[∘] : {X Y Z : Con} {A : TyS n Z} {p : Tms Y Z} {s : Tms X Y}
        → A [ p ∘t s ]TyS ≡ A [ p ]TyS [ s ]TyS
  TyS[∘] {X = X} {Y} {Z} {U n} {p} {s} = refl
  TyS[∘] {X = X} {Y} {Z} {El u} {p} {s} = cong TyS.El (hmerge P)
    where P : (subst (Tm _ X) U[] (u [ p ∘t s ]))
              ⟦ Tm _ X ⟧
              (subst (Tm _ X) U[] (subst (Tm _ Y) U[] (u [ p ]) [ s ]))
          P = subst (Tm _ X) U[] (u [ p ∘t s ])
              ⟮ ‼ sym (subst-filler (Tm _ X) U[] (u [ p ∘t s ])) ⟯
              u [ p ∘t s ]
              ⟮ [∘] ⟯
              u [ p ] [ s ]
              ⟮ ‼ dcong (λ i → i [ s ]) (subst-filler (Tm _ Y) U[] (u [ p ])) ⟯
              subst (Tm _ Y) U[] (u [ p ]) [ s ]
              ⟮ ‼ subst-filler (Tm _ X) U[] (subst (Tm _ Y) U[] (u [ p ]) [ s ]) ⟯
              (subst (Tm _ X) U[] (subst (Tm _ Y) U[] (u [ p ]) [ s ])) □
  TyS[∘] {n} {X = X} {Y} {Z} {Pi A B} {p} {s} = cong₂ TyS.Pi TyS[∘] (hcollapse P (cong (λ i → (X Con., ⌜ i ⌝TyS)) TyS[∘]))
    where P : subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ (p ∘t s) ↑ ⌜ A ⌝TyS ]TyS)
              ⟦ TyS _ ⟧
              (subst (λ i → TyS _ (X , i)) (sym ⌜[]TyS⌝)
                     (subst (λ i → TyS _ (Y , i)) (sym ⌜[]TyS⌝)
                            (B [ p ↑ ⌜ A ⌝TyS ]TyS) [ s ↑ ⌜ A [ p ]TyS ⌝TyS ]TyS))
          P = subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ (p ∘t s) ↑ ⌜ A ⌝TyS ]TyS)
              ⟮ ‼ sym (subst-fill (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ (p ∘t s) ↑ ⌜ A ⌝TyS ]TyS)) ⟯
              B [ (p ∘t s) ↑ ⌜ A ⌝TyS ]TyS
              ⟮ hcong (B [_]TyS) (hsym ↑∘↑) ⟯
              B [ (p ↑ ⌜ A ⌝TyS) ∘t (s ↑ (⌜ A ⌝TyS [ p ]T)) ]TyS
              ⟮ ‼ TyS[∘] ⟯
              B [ p ↑ ⌜ A ⌝TyS ]TyS [ s ↑ (⌜ A ⌝TyS [ p ]T) ]TyS
              ⟮ ‼ dcong (_[ s ↑ _ ]TyS) (subst-fill (λ i → TyS _ (Y , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)) ⟯
              ((subst (λ i → TyS n (Y , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS) [ s ↑ ⌜ A [ p ]TyS ⌝TyS ]TyS))
              ⟮ ‼ subst-fill (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) _ ⟯
              (subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝)
                      (subst (λ i → TyS n (Y , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS) [ s ↑ ⌜ A [ p ]TyS ⌝TyS ]TyS)) □

data evalT : {X : Con} → Ty n X → TyS n X → Set
evalT≡ : {X : Con} {a : Ty n X} {A : TyS n X} → evalT a A → a ≡ ⌜ A ⌝TyS

data evalT where
  evalT[] : {X Y : Con} {u : Ty n Y} {w : TyS n Y} {p : Tms X Y}
          → evalT u w → evalT (u [ p ]T) (w [ p ]TyS)
  evalTU : {X : Con} {n : ℕ} → evalT {X = X} (U n) (U n)
  evalTEl : {X : Con} {u : Tm (suc n) X (U n)} → evalT (El u) (El u)
  evalTPi : {X : Con} {a : Ty n X} {A : TyS n X} {b : Ty n (X , a)} {B : TyS n (X , a)}
         → (ab : evalT a A)
         → (eb : evalT b B)
         → evalT (Pi a b) (Pi A (subst (λ i → TyS n (X , i)) (evalT≡ ab) B))
  isPropEvalT : {X : Con} {a : Ty n X} {A : TyS n X} → isProp (evalT a A)

abstract
  evalT≡ {n} {X} {.(_ [ _ ]T)} {.(_ [ _ ]TyS)} (evalT[] {p = p} ev)
    = cong (_[ p ]T) (evalT≡ ev)
    ∙ sym ⌜[]TyS⌝
  evalT≡ {.(suc _)} {X} {.(U _)} {.(U _)} evalTU = refl
  evalT≡ {n} {X} {.(El _)} {.(El _)} evalTEl = refl
  evalT≡ {n} {X} {.(Pi _ _)} {.(Pi _ _)} (evalTPi {a = a} {A} {b} {B} ea eb)
    = Pi a b
      ≡⟨ cong₂ term.Pi (evalT≡ ea) (hcollapse Q (cong (X ,_) (evalT≡ ea))) ⟩
      Pi ⌜ A ⌝TyS ⌜ subst (λ i → TyS n (X , i)) (evalT≡ ea) B ⌝TyS ∎
      where Q : b ⟦ Ty _ ⟧ ⌜ subst (λ i → TyS n (X , i)) (evalT≡ ea) B ⌝TyS
            Q = b
                ⟮ ‼ evalT≡ eb ⟯
                ⌜ B ⌝TyS
                ⟮ ‼ dcong ⌜_⌝TyS (subst-filler (λ i → TyS n (X , i)) (evalT≡ ea) B) ⟯
                ⌜ subst (λ i → TyS n (X , i)) (evalT≡ ea) B ⌝TyS □
  evalT≡ {n} {X} {a} {A} (isPropEvalT x y i) = isSetTy _ _ (evalT≡ x) (evalT≡ y) i

abstract
  teq : {X : Con} {A : TyS n X} {B : TyS n X} → ⌜ A ⌝TyS ≡ ⌜ B ⌝TyS → A ≡ B
  teq {A = U n} {B = U .n} A≡B = refl
  teq {A = U n} {B = El x} A≡B = absurd (U≢El A≡B)
  teq {A = U n} {B = Pi _ _} A≡B = absurd (U≢Pi A≡B) 
  teq {A = El x} {B = U n} A≡B = absurd (U≢El (sym A≡B))
  teq {A = El x} {B = El y} A≡B = cong TyS.El (El-injective A≡B)
  teq {A = El x} {B = Pi B B₁} A≡B = absurd (El≢Pi A≡B)
  teq {A = Pi A A₁} {B = U n} A≡B = absurd (U≢Pi (sym A≡B))
  teq {A = Pi A A₁} {B = El x} A≡B = absurd (El≢Pi (sym A≡B))
  teq {n} {A = Pi A B} {B = Pi C D} A≡B = teq'
    where AB≡CD : Path (Σ[ A ∈ Ty _ _ ] Ty _ (_ , A)) (⌜ A ⌝TyS , ⌜ B ⌝TyS) (⌜ C ⌝TyS , ⌜ D ⌝TyS)
          AB≡CD = just-injective (cong domains A≡B)
          lemma : ⌜ transport (λ i → TyS n (_ , fst (AB≡CD i))) B ⌝TyS ⟦ Ty _ ⟧ ⌜ D ⌝TyS
          lemma = ⌜ transport (λ i → TyS n (_ , fst (AB≡CD i))) B ⌝TyS
                  ⟮ ‼ dcong ⌜_⌝TyS (sym (transport-filler (λ i → TyS n (_ , fst (AB≡CD i))) B)) ⟯
                  ⌜ B ⌝TyS
                  ⟮ ‼ cong snd (AB≡CD) ⟯
                  ⌜ D ⌝TyS □
          lemma₂ : B ⟦ TyS _ ⟧ D
          lemma₂ = B
                   ⟮ ‼ transport-filler (λ i → TyS n (_ , fst (AB≡CD i))) B ⟯
                   transport (λ i → TyS n (_ , fst (AB≡CD i))) B
                   ⟮ ‼ teq (hmerge lemma) ⟯
                   D □
          teq' : TyS.Pi A B ≡ Pi C D
          teq' with teq (cong fst AB≡CD) -- | teq {!cong snd AB≡CD!}
          teq' | AC = λ i → Pi (AC i) (hcollapse lemma₂ (cong (λ i → (_ , ⌜ i ⌝TyS)) AC) i)

evalTSound : {X : Con} {a : Ty n X} {A B : TyS n X}
          → evalT a A → evalT a B → A ≡ B
evalTSound eA eB = teq (sym (evalT≡ eA) ∙ evalT≡ eB)

normT : {X : Con} → Ty n X → Set
normT {n} {X} ty = Σ[ A ∈ TyS n X ] evalT ty A

isPropNormT : {X : Con} {a : Ty n X} → isProp (normT a)
isPropNormT {a = a} (A , ea) (B , eb) i = evalTSound ea eb i
                                        , isPropPath {B = λ i → evalT a (evalTSound ea eb i)} isPropEvalT ea eb i

open import Proposition

evalTᴹ : Motives
Motives.Tmsᴹ evalTᴹ p = ⊤
Motives.Tmᴹ evalTᴹ u = ⊤
Motives.Tyᴹ evalTᴹ a = normT a

evalTᴿ : Methods evalTᴹ
Methods._[_]Tᴹ evalTᴿ {p = p} (A' , eA) tt = (A' [ p ]TyS) , evalT[] eA
Methods.Uᴹ evalTᴿ {n = n} = (U n) , evalTU
Methods.Elᴹ evalTᴿ {t = t} tt = El t , evalTEl
Methods.Piᴹ evalTᴿ (A' , eA) (B' , eB) = Pi A' (subst (λ i → TyS _ (_ , i)) (evalT≡ eA) B') , evalTPi eA eB
Methods.idtᴹ evalTᴿ = tt
Methods._∘tᴹ_ evalTᴿ tt tt = tt
Methods.εᴹ evalTᴿ = tt
Methods._,ᴹ_ evalTᴿ tt tt = tt
Methods.π₁ᴹ evalTᴿ tt = tt
Methods.π₂ᴹ evalTᴿ tt = tt
Methods._[_]ᴹ evalTᴿ tt tt = tt
Methods.lamᴹ evalTᴿ tt = tt
Methods.appᴹ evalTᴿ tt = tt
Methods.isPropTmsᴹ evalTᴿ tt tt = refl
Methods.isPropTmᴹ evalTᴿ tt tt = refl
Methods.isPropTyᴹ evalTᴿ = isPropNormT

evalT* : {X : Con} (a : Ty n X) → normT a
evalT* = Methods.elimTy evalTᴿ

TyS≡Ty : {X : Con} → TyS n X ≡ Ty n X
TyS≡Ty = isoToPath (iso ⌜_⌝TyS
                   (λ ty → fst (evalT* ty))
                   (λ ty → sym (evalT≡ (snd (evalT* ty))))
                   (λ tys → sym (teq (evalT≡ (snd (evalT* ⌜ tys ⌝TyS))))))

data TySk : Set where
  U : TySk
  El : TySk
--  L : TySk → TySk
  Pi : TySk → TySk → TySk

-- Was too lazy to add skeletons into TyS
data TyP : TySk → ℕ → Con → Set
⌜_⌝TyP : {S : TySk} {n : ℕ} {X : Con} → TyP S n X → Ty n X
TyP→TyS : {S : TySk} {n : ℕ} {X : Con} → TyP S n X → TyS n X

data TyP where
  U : {X : Con} → (n : ℕ) → TyP U (suc n) X
  El : {X : Con} → Tm (suc n) X (U n) → TyP El n X
  Pi : {S T : TySk} {n : ℕ} {X : Con} → (A : TyP S n X) → (B : TyP T n (X , ⌜ A ⌝TyP)) → TyP (Pi S T) n X

⌜ A ⌝TyP = ⌜ TyP→TyS A ⌝TyS

TyP→TyS (U n) = U n
TyP→TyS (El u) = El u
TyP→TyS (Pi A B) = Pi (TyP→TyS A) (TyP→TyS B)

TyS→TyP : {n : ℕ} {X : Con} → (t : TyS n X) → Σ[ S ∈ TySk ] TyP S n X
TyS→TyP≡ : {n : ℕ} {X : Con} → {A : TyS n X} → A ≡ TyP→TyS (snd (TyS→TyP A))

TyS→TyP (U n) = U , U n
TyS→TyP (El u) = El , El u
TyS→TyP (Pi A B) = let
  (S , A') = TyS→TyP A
  (T , B') = TyS→TyP B
  in Pi S T , Pi A' (subst (λ i → TyP T _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ B')

abstract
  TyS→TyP≡ {A = U n} = refl
  TyS→TyP≡ {A = El u} = refl
  TyS→TyP≡ {A = Pi A B} = cong₂ TyS.Pi TyS→TyP≡ (hcollapse P (cong (λ i → (_ Con., ⌜ i ⌝TyS)) TyS→TyP≡))
    where P : B ⟦ TyS _ ⟧ (TyP→TyS (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B))))
          P = B
              ⟮ ‼ TyS→TyP≡ ⟯
              TyP→TyS (snd (TyS→TyP B))
              ⟮ ‼ dcong TyP→TyS (subst-filler (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B))) ⟯
              (TyP→TyS (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B)))) □

private
  handler : Set → Set → Set → TySk → Set
  handler u el pi U = u
  handler u el pi El = el
  handler u el pi (Pi _ _) = pi

  sk-domains : TySk → Maybe (TySk × TySk)
  sk-domains U = nothing
  sk-domains El = nothing
  sk-domains (Pi A B) = just (A , B)

discreteTySk : Discrete TySk
discreteTySk U U = yes refl
discreteTySk U El = no (λ p → absurd (transport (cong (handler ⊤ ⊥ ⊥) p) tt))
discreteTySk U (Pi _ _) = no (λ p → absurd (transport (cong (handler ⊤ ⊥ ⊥) p) tt))
discreteTySk El U = no (λ p → absurd (transport (cong (handler ⊥ ⊤ ⊥) p) tt))
discreteTySk El El = yes refl
discreteTySk El (Pi _ _) = no (λ p → absurd (transport (cong (handler ⊥ ⊤ ⊥) p) tt))
discreteTySk (Pi _ _) U = no (λ p → absurd (transport (cong (handler ⊥ ⊥ ⊤) p) tt))
discreteTySk (Pi _ _) El = no (λ p → absurd (transport (cong (handler ⊥ ⊥ ⊤) p) tt))
discreteTySk (Pi A B) (Pi C D) with discreteTySk A C | discreteTySk B D
... | yes x | yes y = yes (cong₂ Pi x y)
... | yes x | no y = no (λ p → y (cong snd (just-injective (cong sk-domains p))))
... | no x | _ = no (λ p → x (cong fst (just-injective (cong sk-domains p))))

isSetTySk : isSet TySk
isSetTySk = discreteToisSet discreteTySk

instance
  isSetTySk* : IsSet* TySk
  IsSet*.isSet* isSetTySk* = isSetTySk

private instance
  isSetTySkCon* : IsSet* (TySk × Con)
  IsSet*.isSet* isSetTySkCon* = Library.isSetΣ isSetTySk isSetCon

-- Trololol
isSetTyS : {X : Con} → isSet (TyS n X)
isSetTyS {n} {X} = transport (λ i → isSet (TyS≡Ty {n} {X} (~ i))) isSetTy

TyP→TyS≡ : {n : ℕ} {X : Con} → {A : Σ[ S ∈ TySk ] TyP S n X} → TyS→TyP (TyP→TyS (snd A)) ≡ A
TyP→TyS≡ {A = .U , U n} = refl
TyP→TyS≡ {A = .El , El x} = refl
TyP→TyS≡ {n} {X} {A = Pi S T , Pi A B} with TyP→TyS≡ {A = S , A} | TyP→TyS≡ {A = T , B}
... | Z | Z' = λ i → Pi (fst (Z i)) (fst (Z' i))
                    , Pi (snd (Z i)) (transp (λ j → TyP (fst (Z' i)) n (X , ⌜ outS (isSetFillSquare isSetTyS TyS→TyP≡ (λ i → TyP→TyS A) (λ i → TyP→TyS A) (λ i → TyP→TyS (snd (Z i))) i j) ⌝TyS)) i ((snd (Z' i))))

TyP≡TyS : {X : Con} → (Σ[ S ∈ TySk ] (TyP S n X)) ≡ TyS n X
TyP≡TyS = isoToPath (iso (λ (S , A) → TyP→TyS A)
                         (λ A → TyS→TyP A)
                         (λ tys → sym (TyS→TyP≡))
                         λ ty → TyP→TyS≡)

--[]Generic : ((n : ℕ) (X : Con) → Set) → Set
--[]Generic f = {n : ℕ} {X Y : Con} → f n Y → Tms X Y → f n X
              
--[]TyP : {S : TySk} {n : ℕ} {X Y : Con} → TyP S n Y → Tms X Y → Σ[ S ∈ TySk ] TyP S n X
--[]TyP {S} {n} A p = func (S , A) p
--  where func = transport (λ i → []Generic (λ n X → (TyP≡TyS {n} {X} (~ i)))) _[_]TyS

-- We have to write this again because of skeletons
_[_]TyP : {S : TySk} {n : ℕ} {X Y : Con} → TyP S n Y → Tms X Y → TyP S n X
⌜[]TyP⌝ : {S : TySk} {n : ℕ} {X Y : Con} {A : TyP S n Y} {s : Tms X Y}
        → ⌜ A [ s ]TyP ⌝TyP ≡ ⌜ A ⌝TyP [ s ]T

U n [ p ]TyP = U n
El x [ p ]TyP = El (subst (Tm _ _) U[] (x [ p ]))
Pi A B [ p ]TyP = Pi (A [ p ]TyP) (subst (λ i → TyP _ _ (_ , i)) (sym ⌜[]TyP⌝) (B [ p ↑ ⌜ A ⌝TyP ]TyP))

⌜[]TyP⌝ {.U} {.(suc n)} {X} {Y} {U n} {s} = sym U[]
⌜[]TyP⌝ {.El} {n} {X} {Y} {El u} {s} = sym El[]
⌜[]TyP⌝ {Pi S T} {n} {X} {Y} {Pi A B} {s} = hmerge P
  where P : ⌜ Pi (A [ s ]TyP) (subst (λ i → TyP T n (X , i)) (sym ⌜[]TyP⌝) (B [ s ↑ ⌜ A ⌝TyP ]TyP)) ⌝TyP
            ⟦ Ty _ ⟧
            (⌜ Pi A B ⌝TyP [ s ]T)
        P = ⌜ Pi (A [ s ]TyP) (subst (λ i → TyP T n (X , i)) (sym ⌜[]TyP⌝) (B [ s ↑ ⌜ A ⌝TyP ]TyP)) ⌝TyP
            ⟮ ‼ dcong₂ (λ x y → term.Pi x ⌜ y ⌝TyP) ⌜[]TyP⌝ (sym (subst-filler (λ i → TyP T n (X , i)) (sym ⌜[]TyP⌝) (B [ s ↑ ⌜ A ⌝TyP ]TyP))) ⟯
            Pi (⌜ A ⌝TyP [ s ]T) ⌜ B [ s ↑ ⌜ A ⌝TyP ]TyP ⌝TyP
            ⟮ ‼ cong (λ x → term.Pi (⌜ A ⌝TyP [ s ]T) x) ⌜[]TyP⌝ ⟯
            Pi (⌜ A ⌝TyP [ s ]T) (⌜ B ⌝TyP [ s ↑ ⌜ A ⌝TyP ]T)
            ⟮ ‼ sym Pi[] ⟯
            Pi ⌜ A ⌝TyP ⌜ B ⌝TyP [ s ]T □

TyP≡Ty : {X : Con} → (Σ[ S ∈ TySk ] (TyP S n X)) ≡ Ty n X
TyP≡Ty = TyP≡TyS ∙ TyS≡Ty


evsk : {X : Con} (A : Ty n X) → TySk
evsk A = fst (TyS→TyP (fst (evalT* A)))

ev : {X : Con} (A : Ty n X) → TyP (evsk A) n X
ev A = snd (TyS→TyP (fst (evalT* A)))

tyev : {X : Con} {A : Ty n X} → A ≡ ⌜ ev A ⌝TyP
tyev {n} {X} {A} = A
                   ≡⟨ evalT≡ (snd (evalT* A)) ⟩
                   ⌜ fst (evalT* A) ⌝TyS
                   ≡⟨ cong ⌜_⌝TyS TyS→TyP≡ ⟩
                   ⌜ snd (TyS→TyP (fst (evalT* A))) ⌝TyP ∎

evty* : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X} → (S , A) ⟦ (λ i → Σ[ S ∈ TySk ] TyP S n i) ⟧ (evsk ⌜ A ⌝TyP , ev ⌜ A ⌝TyP) 
evty* {S} {n} {X} {A}
      = (S , A)
        ⟮ ‼ sym (TyP→TyS≡ {A = S , A}) ⟯
        TyS→TyP (TyP→TyS A)
        ⟮ ‼ cong TyS→TyP (teq (evalT≡ (snd (evalT* ⌜ A ⌝TyP)))) ⟯
        TyS→TyP (fst (evalT* ⌜ A ⌝TyP))
        ⟮ ‼ cong TyS→TyP TyS→TyP≡ ⟯
        TyS→TyP (TyP→TyS (snd (TyS→TyP (fst (evalT* ⌜ A ⌝TyP)))))
        ⟮ ‼ TyP→TyS≡ {A = evsk ⌜ A ⌝TyP , ev ⌜ A ⌝TyP} ⟯
        (evsk ⌜ A ⌝TyP , ev ⌜ A ⌝TyP) □

evty : {S : TySk} {n : ℕ} {X : Con} {A : TyP S n X} → A ⟦ (λ i → TyP i _ _) ⟧ ev ⌜ A ⌝TyP
evty {S} {n} {X} {A} = ‼ cong snd (hcollapse evty* refl)

TyP-injective : {S : TySk} {n : ℕ} {X : Con} {A B : TyP S n X} → ⌜ A ⌝TyP ≡ ⌜ B ⌝TyP → A ≡ B
TyP-injective {S} {n} {X} {A} {B} p = hmerge P
  where P : A ⟦ (λ i → TyP i _ _) ⟧ B
        P = evty ● ‼ cong ev p ● hsym evty

-- A property of evaluation that we need
_[_]evalT : {X Y : Con} {A : Ty n Y} {B : TyS n Y} → evalT A B → (p : Tms X Y) → evalT (A [ p ]T) (B [ p ]TyS)
evalT[] {u = u} {w = w} {p = p} e [ s ]evalT = transport (λ i → evalT ([∘]T {A = u} {p = p} {v = s} i) (TyS[∘] {A = w} {p = p} {s = s} i)) (e [ p ∘t s ]evalT)
evalTU {n = n} [ s ]evalT = transport (λ i → evalT (U[] {n = n} {p = s} (~ i)) (U _)) evalTU
evalTEl {u = u} [ s ]evalT = transport (λ i → evalT (El[] {u = u} {p = s} (~ i)) (El (subst (Tm _ _) U[] (u [ s ])))) evalTEl
evalTPi {a = a} {A = A} {b = b} {B = B} eA eB [ s ]evalT = transport (λ i → evalT (Pi[] {A = a} {B = b} {p = s} (~ i))
                                                                                    (Pi (A [ s ]TyS) (hmerge P i)))
                                                                     (evalTPi (eA [ s ]evalT) (eB [ s ↑ a ]evalT))
  where P : (subst (λ i → TyS _ (_ , i)) (evalT≡ (eA [ s ]evalT)) (B [ s ↑ a ]TyS))
            ⟦ TyS _ ⟧
            (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (subst (λ i → TyS _ (_ , i)) (evalT≡ eA) B [ s ↑ ⌜ A ⌝TyS ]TyS))
        P = (subst (λ i → TyS _ (_ , i)) (evalT≡ (eA [ s ]evalT)) (B [ s ↑ a ]TyS))
            ⟮ ‼ sym (subst-fill (λ i → TyS _ (_ , i)) (evalT≡ (eA [ s ]evalT)) (B [ s ↑ a ]TyS)) ⟯
            B [ s ↑ a ]TyS
            ⟮ ‼ dcong (λ {k} i → i [ s ↑ evalT≡ eA k ]TyS) (subst-filler (λ i → TyS _ (_ , i)) (evalT≡ eA) B) ⟯
            (subst (λ i → TyS _ (_ , i)) (evalT≡ eA) B [ s ↑ ⌜ A ⌝TyS ]TyS)
            ⟮ ‼ subst-fill (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (subst (λ i → TyS _ (_ , i)) (evalT≡ eA) B [ s ↑ ⌜ A ⌝TyS ]TyS) ⟯
            (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (subst (λ i → TyS _ (_ , i)) (evalT≡ eA) B [ s ↑ ⌜ A ⌝TyS ]TyS)) □
            
isPropEvalT p q i [ s ]evalT = isPropEvalT (p [ s ]evalT) (q [ s ]evalT) i

_[_]normT : {X Y : Con} {A : Ty n Y} → normT A → (p : Tms X Y) → normT (A [ p ]T)
(A , ev) [ s ]normT = (A [ s ]TyS) , (ev [ s ]evalT)

⌜evalT*⌝ : {X Y : Con} {A : Ty n Y} {p : Tms X Y} → fst (evalT* A) [ p ]TyS ≡ fst (evalT* (A [ p ]T))
⌜evalT*⌝ {n} {X} {Y} {A} {p} = teq (sym (evalT≡ (snd (evalT* A) [ p ]evalT)) ∙ evalT≡ (snd (evalT* (A [ p ]T))))

TyS→TyP[] : {X Y : Con} {A : TyS n Y} {p : Tms X Y} → (snd (TyS→TyP A)) [ p ]TyP ⟦ (λ i → TyP i n X) ⟧ snd (TyS→TyP (A [ p ]TyS))
TyS→TyP[] {.(suc n)} {X} {Y} {U n} {p} = hrefl
TyS→TyP[] {n} {X} {Y} {El x} {p} = hrefl
TyS→TyP[] {n} {X} {Y} {Pi A B} {p}
  = ‼ λ i → TyP.Pi {S = type TYPA i} (hcollapse TYPA (type TYPA) i) (hcollapse P (dcong₂ {C = λ _ _ _ → TySk × Con} (λ {k} i j → (i , (Con._,_ {n = n} X (⌜_⌝TyP {S = type TYPA k} j)))) TOGETHER (hcollapse TYPA (type TYPA))) i)
  where TYPA = TyS→TyP[] {n = n} {A = A} {p = p}
        TOGETHER : (fst (TyS→TyP B)) ≡ (fst (TyS→TyP (transp (λ i₁ → TyS n (X , sym ⌜[]TyS⌝ i₁)) i0 (B [ p ↑ ⌜ A ⌝TyS ]TyS))))
        TOGETHER = (fst (TyS→TyP B))
                   ≡⟨ (type (TyS→TyP[] {n = n} {A = B} {p = p ↑ ⌜ A ⌝TyS})) ⟩
                   fst (TyS→TyP (B [ p ↑ ⌜ A ⌝TyS ]TyS))
                   ≡⟨ dcong (λ x → fst (TyS→TyP x)) (subst-filler (λ i → TyS n (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)) ⟩
                   fst (TyS→TyP (subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS))) ∎
        P : (subst (λ i → TyP _ n (_ , i)) (sym ⌜[]TyP⌝) (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B)) [ p ↑ ⌜ snd (TyS→TyP A) ⌝TyP ]TyP))
              ⟦ (λ (x : (TySk × Con)) → TyP (fst x) n (snd x)) ⟧
              (subst (λ i → TyP (fst (TyS→TyP (subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))))
        P = (subst (λ i → TyP (fst (TyS→TyP B)) n (_ , i)) (sym ⌜[]TyP⌝) (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B)) [ p ↑ ⌜ snd (TyS→TyP A) ⌝TyP ]TyP))
               ⟮ pathh (cong {B = λ _ → TySk × Con} (λ y → ((fst (TyS→TyP B)) , (X Con., y))) ⌜[]TyP⌝)
                       (sym (subst-filler (λ i → TyP _ _ (_ , i)) (sym ⌜[]TyP⌝) (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B)) [ p ↑ ⌜ snd (TyS→TyP A) ⌝TyP ]TyP))) ⟯
               (subst (λ i → TyP (fst (TyS→TyP B)) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B)) [ p ↑ ⌜ snd (TyS→TyP A) ⌝TyP ]TyP)
               ⟮ pathh (cong {B = λ _ → TySk × Con} (λ y → fst (TyS→TyP B) , (X , (⌜ y ⌝TyS [ p ]T))) (sym TyS→TyP≡))
                      (dcong (λ {i} x → x [ p ↑ ⌜ TyS→TyP≡ (~ i) ⌝TyS ]TyP) (sym (subst-filler (λ i → TyP _ _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP B))))) ⟯
               (snd (TyS→TyP B)) [ p ↑ ⌜ A ⌝TyS ]TyP
               ⟮ pathh (cong {B = λ _ → TySk × Con} (λ x → (x , (X , (⌜ A ⌝TyS [ p ]T))))  (type (TyS→TyP[] {n = n} {A = B} {p = p ↑ ⌜ A ⌝TyS})))
                       (hcollapse (TyS→TyP[] {n = n} {A = B} {p = p ↑ ⌜ A ⌝TyS} ) (type (TyS→TyP[] {n = n} {A = B} {p = p ↑ ⌜ A ⌝TyS}))) ⟯
               snd (TyS→TyP (B [ p ↑ ⌜ A ⌝TyS ]TyS))
               ⟮ pathh (dcong₂ {C = λ i x y → TySk × Con} (λ x y → (fst (TyS→TyP x)) , (Con._,_ {n = n} X y)) (subst-filler (λ i → TyS n (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS))
                                                                     (sym ⌜[]TyS⌝))
                       (dcong (λ x → snd (TyS→TyP x)) (subst-filler (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))  ⟯
               snd (TyS→TyP (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))
               ⟮ pathh (cong {B = λ _ → TySk × Con} (λ y → (fst (TyS→TyP (subst (λ i → TyS n (X , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))) , (X , ⌜ y ⌝TyS))
                                                                     TyS→TyP≡)
                       (subst-filler (λ i → TyP _ _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS))))) ⟯
               subst (λ i → TyP (fst (TyS→TyP (transp (λ i → TyS n (X , sym ⌜[]TyS⌝ i)) i0 (B [ p ↑ ⌜ A ⌝TyS ]TyS)))) _ (_ , ⌜ i ⌝TyS)) TyS→TyP≡ (snd (TyS→TyP (subst (λ i → TyS _ (_ , i)) (sym ⌜[]TyS⌝) (B [ p ↑ ⌜ A ⌝TyS ]TyS)))) □

⌜[]ev⌝ : {X Y : Con} {A : Ty n Y} {p : Tms X Y} → (ev A) [ p ]TyP ⟦ (λ i → TyP i n X) ⟧ ev (A [ p ]T)
⌜[]ev⌝ {n} {X} {Y} {A} {p}
       = (snd (TyS→TyP (fst (evalT* A))) [ p ]TyP)
         ⟮ TyS→TyP[] {A = fst (evalT* A)} ⟯
         snd (TyS→TyP (fst (evalT* A) [ p ]TyS))
         ⟮ ‼ cong (λ i → snd (TyS→TyP i)) (⌜evalT*⌝ {A = A} {p = p}) ⟯
         snd (TyS→TyP (fst (evalT* (A [ p ]T)))) □
 
[∘]TyP : {S : TySk} {n : ℕ} {X Y Z : Con} {A : TyP S n Z} {s : Tms Y Z} {a : Tms X Y}
       → A [ s ∘t a ]TyP ≡ A [ s ]TyP [ a ]TyP
[∘]TyP {S} {n} {X} {Y} {Z} {A} {s} {a} = hmerge P
  where P : A [ s ∘t a ]TyP ⟦ (λ i → TyP i n X) ⟧ A [ s ]TyP [ a ]TyP
        P = A [ s ∘t a ]TyP
            ⟮ ‼ dcong (_[ s ∘t a ]TyP) (sym (cong snd TyP→TyS≡)) ⟯
            snd (TyS→TyP (TyP→TyS A)) [ s ∘t a ]TyP
            ⟮ TyS→TyP[] {A = TyP→TyS A} ⟯
            snd (TyS→TyP (TyP→TyS A [ s ∘t a ]TyS))
            ⟮ ‼ cong (λ x → snd (TyS→TyP x)) (TyS[∘] {A = TyP→TyS A}) ⟯
            snd (TyS→TyP ((TyP→TyS A [ s ]TyS) [ a ]TyS))
            ⟮ hsym (TyS→TyP[] {A = (TyP→TyS A [ s ]TyS)}) ⟯
            snd (TyS→TyP (TyP→TyS A [ s ]TyS)) [ a ]TyP
            ⟮ hcong (_[ a ]TyP) (hsym (TyS→TyP[] {A = TyP→TyS A})) ⟯
            (snd (TyS→TyP (TyP→TyS A)) [ s ]TyP) [ a ]TyP
            ⟮ ‼ dcong (λ x → x [ s ]TyP [ a ]TyP) (cong snd TyP→TyS≡) ⟯
            (A [ s ]TyP) [ a ]TyP □
