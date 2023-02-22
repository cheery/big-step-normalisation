{-# OPTIONS --cubical #-}
module NormalForm where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
open import Weakening
open import Values

private variable n : ℕ

data Nf : (n : ℕ) (X : Con) → Ty n X → Set
data Nu : (n : ℕ) (X : Con) → Ty n X → Set

⌜_⌝Nf : {X : Con} {A : Ty n X} → Nf n X A → Tm n X A
⌜_⌝Nu : {X : Con} {A : Ty n X} → Nu n X A → Tm n X A

data Nf where
  lam : {X : Con} {A : Ty n X} {B : Ty n (X , A)} → Nf n (X , A) B → Nf n X (Pi A B)
  neuU : {X : Con} → Nu (suc n) X (U n) → Nf (suc n) X (U n)
  neuEl : {X : Con} → {u : Tm (suc n) X (U n)} → Nu n X (El u) → Nf n X (El u)
  --neuL : {X : Con} → {A : Ty n X} → Nu (suc n) X (L A) → Nf (suc n) X (L A)
  nfeq : {X : Con} {A : Ty n X} {x y : Nf n X A} → ⌜ x ⌝Nf ≡ ⌜ y ⌝Nf → x ≡ y
  isSetNf : {X : Con} {A : Ty n X} → isSet (Nf n X A)

data Nu where
  var : {X : Con} {A : Ty n X} → In n X A → Nu n X A
  app : {X : Con} {A : Ty n X} {B : Ty n (X , A)} → Nu n X (Pi A B) → (v : Nf n X A) → Nu n X (B [ < ⌜ v ⌝Nf > ]T)

postulate
  nueq : {X : Con} {A : Ty n X} {n m : Nu n X A} → ⌜ n ⌝Nu ≡ ⌜ m ⌝Nu → n ≡ m

⌜ lam a ⌝Nf = lam ⌜ a ⌝Nf
⌜ neuU x ⌝Nf = ⌜ x ⌝Nu
⌜ neuEl x ⌝Nf = ⌜ x ⌝Nu
--⌜ neuL x ⌝Nf = ⌜ x ⌝Nu
⌜ nfeq xy i ⌝Nf = isSetTm _ _ xy xy i i
⌜ isSetNf x y p q i j ⌝Nf = isSetTm _ _ (λ k → ⌜ p k ⌝Nf) (λ k → ⌜ q k ⌝Nf) i j

⌜ var x ⌝Nu = ⌜ x ⌝In
⌜ app a x ⌝Nu = ⌜ a ⌝Nu $ ⌜ x ⌝Nf

_[_]Nf : {X Y : Con} {A : Ty n Y} (w : Nf n Y A) (s : Wk X Y) → Nf n X (A [ ⌜ s ⌝Wk ]T)
_[_]Nu : {X Y : Con} {A : Ty n Y} (w : Nu n Y A) (s : Wk X Y) → Nu n X (A [ ⌜ s ⌝Wk ]T)

⌜[]Nf⌝ : {X Y : Con} {A : Ty n Y} {w : Nf n Y A} {s : Wk X Y}
      → ⌜ w [ s ]Nf ⌝Nf ≡ ⌜ w ⌝Nf [ ⌜ s ⌝Wk ]
⌜[]Nu⌝ : {X Y : Con} {A : Ty n Y} {w : Nu n Y A} {s : Wk X Y}
      → ⌜ w [ s ]Nu ⌝Nu ≡ ⌜ w ⌝Nu [ ⌜ s ⌝Wk ]

abstract
  [⌜↑⌝] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {s : Wk X Y}
       → B [ ⌜ s ↑Wk A ⌝Wk ]T ≡ B [ ⌜ s ⌝Wk ↑ A ]T
  [⌜↑⌝] {X = X} {Y} {A} {B} {s} = cong (B [_]T) ⌜↑Wk⌝

  [<>][]Nf : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {w : Nf n Y A} {s : Wk X Y}
         → B [ ⌜ s ⌝Wk ↑ A ]T [ < ⌜ w [ s ]Nf ⌝Nf > ]T ≡ B [ < ⌜ w ⌝Nf > ]T [ ⌜ s ⌝Wk ]T
  [<>][]Nf {X = X} {Y} {A} {B} {w} {s}
    = B [ ⌜ s ⌝Wk ↑ A ]T [ < ⌜ w [ s ]Nf ⌝Nf > ]T
      ≡⟨ sym [∘]T ⟩
      (B [ (⌜ s ⌝Wk ↑ A) ∘t < ⌜ w [ s ]Nf ⌝Nf > ]T)
      ≡⟨ cong (B [_]T) (↑∘<> {u = ⌜ w [ s ]Nf ⌝Nf}) ⟩
      (B [ ⌜ s ⌝Wk , ⌜ w [ s ]Nf ⌝Nf ]T)
      ≡⟨ cong (λ x → B [ _ , x ]T) ⌜[]Nf⌝ ⟩
      (B [ ⌜ s ⌝Wk , (⌜ w ⌝Nf [ ⌜ s ⌝Wk ]) ]T)
      ≡⟨ cong (B [_]T) (sym <>∘) ⟩
      B [ < ⌜ w ⌝Nf > ∘t ⌜ s ⌝Wk ]T
      ≡⟨ [∘]T ⟩
      (B [ < ⌜ w ⌝Nf > ]T) [ ⌜ s ⌝Wk ]T ∎

lam x [ s ]Nf = subst (Nf _ _) (sym Pi[]) (lam (tr (Nf _ _) [⌜↑⌝] (x [ s ↑Wk _ ]Nf) ))
neuU x [ s ]Nf = subst (Nf _ _) (sym U[]) (neuU (subst (Nu _ _) U[] (x [ s ]Nu)))
neuEl x [ s ]Nf = subst (Nf _ _) (sym El[]) (neuEl (subst (Nu _ _) El[] (x [ s ]Nu)))
--neuL x [ s ]Nf = subst (Nf _ _) (sym L[]) (neuL (subst (Nu _ _) L[] (x [ s ]Nu)))
nfeq {x = x} {y = y} xy i [ s ]Nf = P i
  where P : x [ s ]Nf ≡ y [ s ]Nf
        P = nfeq (⌜[]Nf⌝ ∙ cong (_[ ⌜ s ⌝Wk ]) xy ∙ sym ⌜[]Nf⌝)
isSetNf x y x≡y1 x≡y2 i j [ s ]Nf = isSetNf _ _ (λ k → x≡y1 k [ s ]Nf) (λ k → x≡y2 k [ s ]Nf) i j

var x [ s ]Nu = var (x [ s ]In)
app x v [ s ]Nu = tr (Nu _ _) ([<>][]Nf {w = v}) (app (subst (Nu _ _) Pi[] (x [ s ]Nu)) (v [ s ]Nf))

⌜[]Nf⌝ {X = X} {Y} {.(Pi _ _)} {lam {A = A} w} {s} = hmerge P
  where P : ⌜ subst (Nf _ X) (sym Pi[]) (lam (tr (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf))) ⌝Nf
            ⟦ Tm _ _ ⟧
            (lam ⌜ w ⌝Nf [ ⌜ s ⌝Wk ])
        Q : ⌜ tr (In _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜weakener⌝] Zero ⌝In
            ⟦ Tm _ _ ⟧
            subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) (π₂ idt)
        Q = ⌜ tr (In _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜weakener⌝] Zero ⌝In
            ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ _) [⌜weakener⌝] Zero)) ⟯
            π₂ idt
            ⟮ ‼ subst-filler (Tm _ _) (sym [∘]T) (π₂ idt) ⟯
            subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) (π₂ idt) □
        P = ⌜ subst (Nf _ X) (sym Pi[]) (lam (tr (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf))) ⌝Nf
            ⟮ ‼ dcong ⌜_⌝Nf (sym (subst-filler (Nf _ X) (sym Pi[]) (lam (tr (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf))))) ⟯
            (lam ⌜ tr (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf) ⌝Nf)
            ⟮ ‼ dcong (λ x → term.lam ⌜ x ⌝Nf) (sym (trfill (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf))) ⟯
            lam ⌜ w [ s ↑Wk A ]Nf ⌝Nf
            ⟮ ‼ dcong term.lam (⌜[]Nf⌝ {w = w} {s = s ↑Wk A}) ⟯
            (lam (⌜ w ⌝Nf [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk , ⌜ tr (In _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜weakener⌝] Zero ⌝In ]))
            ⟮ ‼ dcong₂ (λ x y → term.lam (⌜ w ⌝Nf [ x , y ])) ⌜weakener⌝ (hcollapse Q (cong (A [_]T) ⌜weakener⌝)) ⟯
            (lam (⌜ w ⌝Nf [ (⌜ s ⌝Wk ∘t π₁ idt) , subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) (π₂ idt) ]))
            ⟮ ‼ subst-fill (Tm _ X) (sym Pi[]) (lam (⌜ w ⌝Nf [ (⌜ s ⌝Wk ∘t π₁ idt) , subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) (π₂ idt) ])) ⟯
            (subst (Tm _ X) (sym Pi[]) (lam (⌜ w ⌝Nf [ (⌜ s ⌝Wk ∘t π₁ idt) , subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) (π₂ idt) ])))
            ⟮ ‼ sym lam[] ⟯
            (lam ⌜ w ⌝Nf [ ⌜ s ⌝Wk ]) □
⌜[]Nf⌝ {X = X} {Y} {.(U _)} {neuU x} {s} = hmerge P
  where P : ⌜ subst (Nf (suc _) X) (sym U[]) (neuU (subst (Nu (suc _) X) U[] (x [ s ]Nu))) ⌝Nf
            ⟦ Tm _ _ ⟧
            (⌜ x ⌝Nu [ ⌜ s ⌝Wk ])
        P = ⌜ subst (Nf (suc _) X) (sym (U[] {p = ⌜ s ⌝Wk})) (neuU (subst (Nu (suc _) X) U[] (x [ s ]Nu))) ⌝Nf
            ⟮ ‼ dcong ⌜_⌝Nf (sym (subst-filler (Nf _ X) (sym U[]) (neuU (subst (Nu (suc _) X) U[] (x [ s ]Nu))))) ⟯
            ⌜ subst (Nu (suc _) X) U[] (x [ s ]Nu) ⌝Nu
            ⟮ ‼ dcong ⌜_⌝Nu (sym (subst-filler (Nu _ X) U[] (x [ s ]Nu))) ⟯
            ⌜ x [ s ]Nu ⌝Nu
            ⟮ ‼ ⌜[]Nu⌝ {w = x} ⟯
            ⌜ x ⌝Nu [ ⌜ s ⌝Wk ] □
⌜[]Nf⌝ {X = X} {Y} {.(El _)} {neuEl x} {s} = hmerge P
  where P : ⌜ subst (Nf _ X) (sym El[]) (neuEl (subst (Nu _ X) El[] (x [ s ]Nu))) ⌝Nf
            ⟦ Tm _ _ ⟧
            (⌜ x ⌝Nu [ ⌜ s ⌝Wk ])
        P = ⌜ subst (Nf _ X) (sym (El[] {p = ⌜ s ⌝Wk})) (neuEl (subst (Nu _ X) El[] (x [ s ]Nu))) ⌝Nf
            ⟮ ‼ dcong ⌜_⌝Nf (sym (subst-filler (Nf _ X) (sym El[]) (neuEl (subst (Nu _ X) El[] (x [ s ]Nu))))) ⟯
            ⌜ subst (Nu _ X) El[] (x [ s ]Nu) ⌝Nu
            ⟮ ‼ dcong ⌜_⌝Nu (sym (subst-filler (Nu _ X) El[] (x [ s ]Nu))) ⟯
            ⌜ x [ s ]Nu ⌝Nu
            ⟮ ‼ ⌜[]Nu⌝ {w = x} ⟯
            ⌜ x ⌝Nu [ ⌜ s ⌝Wk ] □
{--⌜[]Nf⌝ {X = X} {Y} {.(L _)} {neuL x} {s} = hmerge P
  where P : ⌜ subst (Nf _ X) (sym L[]) (neuL (subst (Nu _ X) L[] (x [ s ]Nu))) ⌝Nf
            ⟦ Tm _ _ ⟧
            (⌜ x ⌝Nu [ ⌜ s ⌝Wk ])
        P = ⌜ subst (Nf _ X) (sym (L[] {p = ⌜ s ⌝Wk})) (neuL (subst (Nu _ X) L[] (x [ s ]Nu))) ⌝Nf
            ⟮ ‼ dcong ⌜_⌝Nf (sym (subst-filler (Nf _ X) (sym L[]) (neuL (subst (Nu _ X) L[] (x [ s ]Nu))))) ⟯
            ⌜ subst (Nu _ X) L[] (x [ s ]Nu) ⌝Nu
            ⟮ ‼ dcong ⌜_⌝Nu (sym (subst-filler (Nu _ X) L[] (x [ s ]Nu))) ⟯
            ⌜ x [ s ]Nu ⌝Nu
            ⟮ ‼ ⌜[]Nu⌝ {w = x} ⟯
            ⌜ x ⌝Nu [ ⌜ s ⌝Wk ] □--}
⌜[]Nf⌝ {n} {X = X} {Y} {A} {nfeq {x = x} {y = y} xy i} {s} k = square k i
  where eq₁ : (i : I) → Tm _ X (A [ ⌜ s ⌝Wk ]T)
        eq₁ i = isSetTm ⌜ x [ s ]Nf ⌝Nf ⌜ y [ s ]Nf ⌝Nf
                         (⌜[]Nf⌝ {w = x} ∙ (λ i₁ → xy i₁ [ ⌜ s ⌝Wk ]) ∙ sym (⌜[]Nf⌝ {w = y}))
                         (⌜[]Nf⌝ {w = x} ∙ (λ i₁ → xy i₁ [ ⌜ s ⌝Wk ]) ∙ sym (⌜[]Nf⌝ {w = y})) i i
        eq₂ : (i : I) → Tm _ X (A [ ⌜ s ⌝Wk ]T)
        eq₂ i = isSetTm ⌜ x ⌝Nf ⌜ y ⌝Nf xy xy i i [ ⌜ s ⌝Wk ]
        square : PathP (λ k → ⌜[]Nf⌝ {w = x} {s = s} k ≡ ⌜[]Nf⌝ {w = y} {s = s} k) (λ i → eq₁ i) (λ i → eq₂ i)
        square i j = outS (isSetFillSquare isSetTm (λ i → eq₁ i) (λ i → eq₂ i) (⌜[]Nf⌝ {w = x}) (⌜[]Nf⌝ {w = y}) i j)
⌜[]Nf⌝ {X = X} {Y} {A} {isSetNf x y p q i j} {s} k
  = outS (isSetPartial isSetTm
                        (λ j → ⌜[]Nf⌝ {w = p j} {s} k)
                        ((λ j → ⌜[]Nf⌝ {w = q j} {s} k))
                        λ {(k = i0) → λ i j →
                            ⌜ isSetNf _ _ (λ j → p j [ s ]Nf) (λ j → q j [ s ]Nf) i j ⌝Nf
                           ;(k = i1) → λ i j →
                            ⌜ isSetNf _ _ p q i j ⌝Nf [ ⌜ s ⌝Wk ] })
          i j

⌜[]Nu⌝ {X = X} {Y} {A} {var x} {s} = ⌜[]In⌝
⌜[]Nu⌝ {X = X} {Y} {.(_ [ < ⌜ v ⌝Nf > ]T)} {app w v} {s} = hmerge P
  where P : ⌜ tr (Nu _ X) [<>][]Nf (app (subst (Nu _ X) Pi[] (w [ s ]Nu)) (v [ s ]Nf)) ⌝Nu
            ⟦ Tm _ _ ⟧
            ((⌜ w ⌝Nu $ ⌜ v ⌝Nf) [ ⌜ s ⌝Wk ])
        Q : ⌜ subst (Nu _ X) Pi[] (w [ s ]Nu) ⌝Nu
            ⟦ Tm _ X ⟧
            subst (Tm _ X) Pi[] ⌜ w [ s ]Nu ⌝Nu
        P = ⌜ tr (Nu _ X) [<>][]Nf (app (subst (Nu _ X) Pi[] (w [ s ]Nu)) (v [ s ]Nf)) ⌝Nu
            ⟮ ‼ dcong ⌜_⌝Nu (sym (trfill (Nu _ X) [<>][]Nf _)) ⟯
            ⌜ app (subst (Nu _ X) Pi[] (w [ s ]Nu)) (v [ s ]Nf) ⌝Nu
            ⟮ hrefl ⟯
            (⌜ subst (Nu _ X) Pi[] (w [ s ]Nu) ⌝Nu $ ⌜ v [ s ]Nf ⌝Nf)
            ⟮ ‼ cong (_$ ⌜ v [ s ]Nf ⌝Nf) (hmerge Q) ⟯
            (subst (Tm _ X) Pi[] ⌜ w [ s ]Nu ⌝Nu $ ⌜ v [ s ]Nf ⌝Nf)
            ⟮ ‼ dcong (λ x → subst (Tm _ X) Pi[] x $ ⌜ v [ s ]Nf ⌝Nf) (⌜[]Nu⌝ {w = w}) ⟯
            (subst (Tm _ X) Pi[] (⌜ w ⌝Nu [ ⌜ s ⌝Wk ]) $ ⌜ v [ s ]Nf ⌝Nf)
            ⟮ ‼ dcong (subst (Tm _ X) Pi[] (⌜ w ⌝Nu [ ⌜ s ⌝Wk ]) $_) (⌜[]Nf⌝ {w = v}) ⟯
            ( (subst (Tm _ X) Pi[] (⌜ w ⌝Nu [ ⌜ s ⌝Wk ]) $ (⌜ v ⌝Nf [ ⌜ s ⌝Wk ])))
            ⟮ hsym $[] ⟯
            (⌜ w ⌝Nu $ ⌜ v ⌝Nf) [ ⌜ s ⌝Wk ] □
        Q = ⌜ subst (Nu _ X) Pi[] (w [ s ]Nu) ⌝Nu
            ⟮ ‼ dcong ⌜_⌝Nu (sym (subst-filler (Nu _ X) Pi[] (w [ s ]Nu))) ⟯
            ⌜ w [ s ]Nu ⌝Nu
            ⟮ ‼ subst-filler (Tm _ X) Pi[] ⌜ w [ s ]Nu ⌝Nu ⟯
            subst (Tm _ X) Pi[] ⌜ w [ s ]Nu ⌝Nu □
