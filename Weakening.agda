{-# OPTIONS --cubical #-}
module Weakening where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas

private variable n m : ℕ

data In : (n : ℕ) → (X : Con) → Ty n X → Set where
  Zero : {X : Con} {A : Ty n X} → In n (X , A) (A [ wk ]T)
  Suc : {X : Con} {A : Ty n X} {B : Ty m X} → In n X A → In n (X , B) (A [ wk ]T)

⌜_⌝In : {X : Con} {A : Ty n X} → In n X A → Tm n X A
⌜ Zero ⌝In = vz
⌜ Suc a ⌝In = vs ⌜ a ⌝In

Wk : Con → Con → Set
⌜_⌝Wk : {X Y : Con} → Wk X Y → Tms X Y

data WkR (n : ℕ) (X : Con) (Y : Con) (A : Ty n Y) : Set where
  _,_ : (s : Wk X Y) → In n X (A [ ⌜ s ⌝Wk ]T) → WkR n X Y A

Wk X ∅ = ⊤
Wk X (Y , A) = WkR (universe A) X Y A

⌜_⌝Wk {Y = ∅} x = ε
⌜_⌝Wk {Y = Y , A} (p , x) = ⌜ p ⌝Wk , ⌜ x ⌝In

{--
postulate
  weakener : {X Y : Con} (A : Ty n X) → Wk X Y → Wk (X , A) Y
  idwk : {X : Con} → Wk X X
  _[_]In : {X Y : Con} {A : Ty n Y} → In Y A → (p : Wk X Y) → In X (A [ ⌜ p ⌝Wk ]T)
  _○_ : {X Y Z : Con} → Wk Y Z → Wk X Y → Wk X Z

  ⌜weakener⌝ : {X Y : Con} {A : Ty n X} {p : Wk X Y}
             → ⌜ weakener A p ⌝Wk ≡ ⌜ p ⌝Wk ∘t (π₁ idt)
  ⌜idwk⌝ : {X : Con} → ⌜ idwk {X} ⌝Wk ≡ idt
  ⌜[]In⌝ : {X Y : Con} {A : Ty n Y} {x : In Y A} {p : Wk X Y}
    → ⌜ x [ p ]In ⌝In ≡ ⌜ x ⌝In [ ⌜ p ⌝Wk ]
  ⌜○⌝ : {X Y Z : Con} {p : Wk Y Z} {s : Wk X Y}
      → ⌜ p ○ s ⌝Wk ≡ ⌜ p ⌝Wk ∘t ⌜ s ⌝Wk
--}

weakener : {X Y : Con} (A : Ty n X) → Wk X Y → Wk (X , A) Y
idwk : {X : Con} → Wk X X
_[_]In : {X Y : Con} {A : Ty n Y} → In n Y A → (p : Wk X Y) → In n X (A [ ⌜ p ⌝Wk ]T)
_○_ : {X Y Z : Con} → Wk Y Z → Wk X Y → Wk X Z

⌜weakener⌝ : {X Y : Con} {A : Ty n X} {p : Wk X Y}
          → ⌜ weakener A p ⌝Wk ≡ ⌜ p ⌝Wk ∘t (π₁ idt)
⌜idwk⌝ : {X : Con} → ⌜ idwk {X} ⌝Wk ≡ idt
⌜[]In⌝ : {X Y : Con} {A : Ty n Y} {x : In n Y A} {p : Wk X Y}
      → ⌜ x [ p ]In ⌝In ≡ ⌜ x ⌝In [ ⌜ p ⌝Wk ]
⌜○⌝ : {X Y Z : Con} {p : Wk Y Z} {s : Wk X Y}
   → ⌜ p ○ s ⌝Wk ≡ ⌜ p ⌝Wk ∘t ⌜ s ⌝Wk

abstract
  weakener-lemma : {X Y : Con} {A : Ty n X} {B : Ty m Y} {p : Wk X Y}
                 → (B [ ⌜ p ⌝Wk ]T [ wk ]T) ≡ B [ ⌜ weakener A p ⌝Wk ]T
  weakener-lemma {X = X} {Y} {A} {B} {p} = (B [ ⌜ p ⌝Wk ]T [ wk ]T)
                                           ≡⟨ sym [∘]T ⟩
                                           B [ ⌜ p ⌝Wk ∘t wk ]T
                                           ≡⟨ cong (B [_]T) (sym (⌜weakener⌝ {p = p})) ⟩
                                           B [ ⌜ weakener A p ⌝Wk ]T ∎

weakener {Y = ∅} A p = tt
weakener {Y = Y , B} A (p , x) = weakener A p , tr (In _ (_ , A)) weakener-lemma (Suc x)

abstract
  idwk-lemma : {X : Con} {A : Ty n X}
             → A [ wk ]T ≡ A [ ⌜ weakener A idwk ⌝Wk ]T
  idwk-lemma {X = X} {A} = A [ wk ]T
                     ≡⟨ cong (A [_]T) (sym id∘) ⟩
                     (A [ idt ∘t wk ]T)
                     ≡⟨ cong (λ p → A [ p ∘t wk ]T) (sym ⌜idwk⌝) ⟩
                     A [ ⌜ idwk ⌝Wk ∘t wk ]T
                     ≡⟨ cong (A [_]T) (sym ⌜weakener⌝) ⟩
                     A [ ⌜ weakener A idwk ⌝Wk ]T ∎

idwk {∅} = tt
idwk {X , A} = weakener A idwk , tr (In _ (X , A)) idwk-lemma Zero

abstract
  weakening-lemma : {X Y : Con} {A : Ty m Y} {B : Ty n Y} {p : Wk X Y} {x : In n X (B [ ⌜ p ⌝Wk ]T)}
    → A [ ⌜ p ⌝Wk ]T ≡ (A [ wk ]T) [ ⌜ p ⌝Wk , ⌜ x ⌝In ]T
  weakening-lemma {X = X} {Y} {A} {B} {p} {x} = (A [ ⌜ p ⌝Wk ]T)
                  ≡⟨ cong (A [_]T) (sym π₁β) ⟩
                  (A [ π₁ (⌜ p ⌝Wk , ⌜ x ⌝In) ]T)
                  ≡⟨ cong (λ p → A [ π₁ p ]T) (sym id∘) ⟩
                  (A [ π₁ (idt ∘t (⌜ p ⌝Wk , ⌜ x ⌝In)) ]T)
                  ≡⟨ cong (A [_]T) π₁∘ ⟩
                  (A [ wk ∘t (⌜ p ⌝Wk , ⌜ x ⌝In) ]T)
                  ≡⟨ [∘]T ⟩
                  (A [ wk ]T) [ ⌜ p ⌝Wk , ⌜ x ⌝In ]T ∎

_[_]In {X = X} (Zero {A = A}) (p , x) = tr (In _ X) (weakening-lemma {x = x}) x
_[_]In {X = X} (Suc n) (p , x) = tr (In _ X) (weakening-lemma {x = x}) (n [ p ]In)

abstract
  ○-lemma : {X Y Z : Con} {A : Ty n Z} {p : Wk Y Z} {q : Wk X Y}
          → ((A [ ⌜ p ⌝Wk ]T) [ ⌜ q ⌝Wk ]T) ≡ A [ ⌜ p ○ q ⌝Wk ]T
  ○-lemma {X = X} {Y} {Z} {A} {p} {q} = (A [ ⌜ p ⌝Wk ]T) [ ⌜ q ⌝Wk ]T
                                    ≡⟨ sym [∘]T ⟩
                                    A [ ⌜ p ⌝Wk ∘t ⌜ q ⌝Wk ]T
                                    ≡⟨ cong (A [_]T) (sym ⌜○⌝) ⟩
                                    A [ ⌜ p ○ q ⌝Wk ]T ∎

_○_ {Z = ∅} p q = tt
_○_ {Z = Z , A} (p , x) q = p ○ q , tr (In _ _) ○-lemma (x [ q ]In)

abstract
  ⌜weakener⌝ {X = X} {∅} {A} {tt} = sym (εη)
  ⌜weakener⌝ {X = X} {Y , B} {A} {(p , x)} = hmerge P
    where P : ⌜ ⟨ Wk (X , A) (Y , B) ⟩ (weakener A p , tr (In _ _) weakener-lemma (Suc x)) ⌝Wk
              ⟦ Tms (X , A) ⟧
              ⌜ ⟨ Wk X (Y , B) ⟩ (p , x) ⌝Wk ∘t (π₁ idt)
          Q : ⌜ tr (In _ _) weakener-lemma (Suc x) ⌝In
              ⟦ Tm _ (X , A) ⟧
              subst (Tm _ _) (sym [∘]T) ⌜ Suc x ⌝In
          P = (⌜ weakener A p ⌝Wk , ⌜ tr (In _ _) weakener-lemma (Suc x) ⌝In)
              ⟮ ‼ (λ i → ⌜weakener⌝ {A = A} {p = p} i , hcollapse Q (cong (B [_]T) ⌜weakener⌝) i) ⟯
              ((⌜ p ⌝Wk ∘t wk) , subst (Tm _ _) (sym [∘]T) ⌜ Suc x ⌝In)
              ⟮ ‼ sym ,∘ ⟯
              ⌜ p , x ⌝Wk ∘t (π₁ idt) □
          Q = ⌜ tr (In _ _) weakener-lemma (Suc x) ⌝In
              ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ _) weakener-lemma (Suc x))) ⟯
              ⌜ Suc x ⌝In
              ⟮ ‼ subst-fill (Tm _ _) (sym [∘]T) ⌜ Suc x ⌝In ⟯
              subst (Tm _ _) (sym [∘]T) ⌜ Suc x ⌝In □

  ⌜idwk⌝ {∅} = sym εη
  ⌜idwk⌝ {X , A} = hmerge P
    where P : (⌜ weakener A idwk ⌝Wk , ⌜ tr (In _ (X , A)) idwk-lemma Zero ⌝In)
              ⟦ Tms (X , A) ⟧
              idt
          Q : ⟨ Tm _ (X , A) (A [ ⌜ weakener A idwk ⌝Wk ]T) ⟩ ⌜ tr (In _ (X , A)) idwk-lemma Zero ⌝In
              ⟦ Tm _ (X , A) ⟧
              ⟨ Tm _ (X , A) (A [ π₁ idt ]T) ⟩ vz
          Q = ⌜ tr (In _ (X , A)) idwk-lemma Zero ⌝In
              ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ _) idwk-lemma Zero)) ⟯
              vz □
          R : ⌜ weakener A (idwk {X = X}) ⌝Wk ≡ π₁ idt
          R = ⌜ weakener A idwk ⌝Wk
              ≡⟨ ⌜weakener⌝ ⟩
              ⌜ idwk ⌝Wk ∘t π₁ idt
              ≡⟨ cong (_∘t wk) ⌜idwk⌝ ⟩
              idt ∘t wk
              ≡⟨ id∘ ⟩
              wk ∎
          P = ((⌜ weakener A idwk ⌝Wk , ⌜ tr (In _ (X , A)) idwk-lemma Zero ⌝In))
              ⟮ ‼ (λ i → R i , hcollapse Q (cong (A [_]T) R) i) ⟯
              (π₁ idt , π₂ idt)
              ⟮ ‼ πη ⟯
              idt □

  ⌜[]In⌝ {X = X} {.(_ , _)} {.(_ [ wk ]T)} {Zero} {p , x} = hmerge P
    where P : ⌜ tr (In _ X) (weakening-lemma {x = x}) x ⌝In
               ⟦ Tm _ X ⟧
               (vz [ ⌜ p ⌝Wk , ⌜ x ⌝In ])
          P = ⌜ tr (In _ X) (weakening-lemma {x = x}) x ⌝In
              ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ X) (weakening-lemma {x = x}) x)) ⟯
              ⌜ x ⌝In
              ⟮ hsym vz[,] ⟯
              ((vz [ ⌜ p ⌝Wk , ⌜ x ⌝In ])) □
  ⌜[]In⌝ {z} {X = X} {.(_ , _)} {.(_ [ wk ]T)} {Suc {m = m} n} {p , x} = hmerge P
    where P : ⌜ tr (In _ X) (weakening-lemma {x = x}) (n [ p ]In) ⌝In
              ⟦ Tm z X ⟧
              (vs ⌜ n ⌝In [ ⌜ p ⌝Wk , ⌜ x ⌝In ])
          P = ⌜ tr (In _ X) (weakening-lemma {x = x}) (n [ p ]In) ⌝In
              ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ X) (weakening-lemma {x = x}) (n [ p ]In))) ⟯
              ⌜ n [ p ]In ⌝In
              ⟮ ‼ ⌜[]In⌝ {x = n} ⟯
              (⌜ n ⌝In [ ⌜ p ⌝Wk ])
              ⟮ ‼ dcong (λ p → ⌜ n ⌝In [ p ]) (sym wk,) ⟯
              (⌜ n ⌝In [ wk ∘t (⌜ p ⌝Wk , ⌜ x ⌝In) ])
              ⟮ [∘] ⟯
              (vs ⌜ n ⌝In [ ⌜ p ⌝Wk , ⌜ x ⌝In ]) □
                  
  ⌜○⌝ {X = X} {Y} {∅} {tt} {s} = sym εη
  ⌜○⌝ {X = X} {Y} {(_ , A)} {q , x} {s} = hmerge P
    where P : (⌜ q ○ s ⌝Wk , ⌜ tr (In _ X) ○-lemma (x [ s ]In) ⌝In)
              ⟦ Tms X ⟧
              (⌜ q ⌝Wk , ⌜ x ⌝In) ∘t ⌜ s ⌝Wk
          Q : ⟨ Tm _ X (A [ ⌜ q ○ s ⌝Wk ]T) ⟩ ⌜ tr (In _ X) ○-lemma (x [ s ]In) ⌝In
              ⟦ Tm _ X ⟧
              ⟨ Tm _ X (A [ ⌜ q ⌝Wk ∘t ⌜ s ⌝Wk ]T) ⟩ subst (Tm _ X) (sym [∘]T) (⌜ x ⌝In [ ⌜ s ⌝Wk ])
          P = (⌜ q ○ s ⌝Wk , ⌜ tr (In _ X) ○-lemma (x [ s ]In) ⌝In)
               ⟮ ‼ (λ i → ⌜○⌝ {p = q} {s = s} i , hcollapse Q (cong (A [_]T) ⌜○⌝) i ) ⟯
               (((⌜ q ⌝Wk ∘t ⌜ s ⌝Wk) , (subst (Tm _ X) (sym [∘]T) (⌜ x ⌝In [ ⌜ s ⌝Wk ]))))
               ⟮ ‼ sym ,∘ ⟯
               (⌜ q ⌝Wk , ⌜ x ⌝In) ∘t ⌜ s ⌝Wk □
          Q = ⌜ tr (In _ X) ○-lemma (x [ s ]In) ⌝In
               ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ X) ○-lemma (x [ s ]In))) ⟯
               ⌜ x [ s ]In ⌝In
               ⟮ ‼ (⌜[]In⌝ {x = x}) ⟯
               ⌜ x ⌝In [ ⌜ s ⌝Wk ]
               ⟮ ‼ subst-fill (Tm _ X) (sym [∘]T) _ ⟯
               subst (Tm _ X) (sym [∘]T) (⌜ x ⌝In [ ⌜ s ⌝Wk ]) □

abstract
  [⌜weakener⌝] : {X Y : Con} {A : Ty n Y} {s : Wk X Y}
              → A [ ⌜ s ⌝Wk ]T [ wk {A = A [ ⌜ s ⌝Wk ]T} ]T ≡ A [ ⌜ weakener _ s ⌝Wk ]T
  [⌜weakener⌝] {X = X} {Y} {A} {s}
    = A [ ⌜ s ⌝Wk ]T [ wk {A = A [ ⌜ s ⌝Wk ]T} ]T
      ≡⟨ sym [∘]T ⟩
      A [ ⌜ s ⌝Wk ∘t wk ]T
      ≡⟨ cong (A [_]T) (sym ⌜weakener⌝) ⟩
      A [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk ]T ∎

_↑Wk_ : {X Y : Con} (s : Wk X Y) (A : Ty n Y)
     → Wk (X , A [ ⌜ s ⌝Wk ]T) (Y , A)
s ↑Wk A = weakener _ s , tr (In _ _) [⌜weakener⌝] Zero

⌜↑Wk⌝ : {X Y : Con} {A : Ty n Y} {s : Wk X Y} → ⌜ s ↑Wk A ⌝Wk ≡ ⌜ s ⌝Wk ↑ A
⌜↑Wk⌝ {X = X} {Y} {A} {s}
  = (⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk , ⌜ tr (In _ _) [⌜weakener⌝] Zero ⌝In)
     ≡⟨ cong₂ term._,_ P (hcollapse Q (cong (A [_]T) P)) ⟩
     ((⌜ s ⌝Wk ∘t π₁ idt) , subst (Tm _ _) (sym [∘]T) (π₂ idt)) ∎
    where P : ⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk ≡ ⌜ s ⌝Wk ∘t wk
          P = ⌜weakener⌝
          Q : ⌜ tr (In _ _) [⌜weakener⌝] Zero ⌝In
              ⟦ Tm _ (X , A [ ⌜ s ⌝Wk ]T) ⟧
              subst (Tm _ _) (sym [∘]T) vz
          Q = ⌜ tr (In _ _) [⌜weakener⌝] Zero ⌝In
              ⟮ ‼ dcong ⌜_⌝In (sym (trfill (In _ _) [⌜weakener⌝] Zero)) ⟯
              π₂ idt
              ⟮ ‼ subst-filler (Tm _ _) (sym [∘]T) vz ⟯
              (subst (Tm _ (X , (A [ ⌜ s ⌝Wk ]T))) (sym [∘]T) vz) □
