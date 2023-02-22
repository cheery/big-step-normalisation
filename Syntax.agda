{-# OPTIONS --cubical #-}
module Syntax where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library

private variable n : ℕ

data term-index : Set
data Con : Set
data term : term-index → Set

data term-index where
  Ty-i : ℕ → Con → term-index
  Tm-i : (n : ℕ) → (X : Con) → term (Ty-i n X) → term-index
  Tms-i : Con → Con → term-index

Ty : ℕ → Con → Set
Ty n X = term (Ty-i n X)

Tm : (n : ℕ) → (X : Con) → Ty n X → Set
Tm n X A = term (Tm-i n X A)

Tms : Con → Con → Set
Tms X A = term (Tms-i X A)

data Con where
  ∅ : Con
  _,_ : {n : ℕ} → (X : Con) → Ty n X → Con

-- To allow induction on terms, we have to help the termination checker with this box
record Box (i : term-index) : Set where
  constructor box
  inductive
  field
    unbox : term i
open Box

data term where
  -- Type constructors
  _[_]T : {X Y : Con} → Ty n Y → Tms X Y → Ty n X
  U : {X : Con} (n : ℕ) → Ty (suc n) X
  El : {X : Con} → Tm (suc n) X (U n) → Ty n X
  Pi : {X : Con} → (A : Ty n X) → Ty n (X , A) → Ty n X
  --L : {X : Con} → Ty n X → Ty (suc n) X
  -- Substitution constructors
  idt : {X : Con} → Tms X X
  _∘t_ : {X Y Z : Con} → Tms Y Z → Tms X Y → Tms X Z
  ε : {X : Con} → Tms X ∅
  _,_ : {X Y : Con} → {A : Ty n Y} → (p : Tms X Y) → Tm n X (A [ p ]T) → Tms X (Y , A)
  π₁ : {X Y : Con} → {A : Ty n Y} → Tms X (Y , A) → Tms X Y
  -- Tm constructors
  π₂-boxed : {X Y : Con} → {A : Ty n Y} → (p : Box (Tms-i X (Y , A))) → Tm n X (A [ π₁ (unbox p) ]T)
  _[_]-boxed : {X Y : Con} → {A : Ty n Y} → Tm n Y A → (p : Box (Tms-i X Y)) → Tm n X (A [ unbox p ]T)
  lam : {X : Con} {A : Ty n X} → {B : Ty n (X , A)} → Tm n (X , A) B → Tm n X (Pi A B)
  app : {X : Con} → {A : Ty n X} → {B : Ty n (X , A)} → Tm n X (Pi A B) → Tm n (X , A) B
  -- Type formers
  {--
  U^ : {X : Con} → (n : ℕ) → Tm (suc (suc n)) X (U (suc n))
  Pi^ : {X : Con} → (A : Tm (suc n) X (U n))
                  → (B : Tm (suc n) (X , El A) (U n))
                  → Tm (suc n) X (U n)
  L^ : {X : Con} → Tm (suc n) X (U n) → Tm (suc (suc n)) X (U (suc n)) --}
  -- Type equations
  [id]T : {X : Con} {A : Ty n X} → A [ idt ]T ≡ A
  [∘]T : {X Y Z : Con} {A : Ty n Z} {p : Tms Y Z} {v : Tms X Y}
      → A [ p ∘t v ]T ≡ A [ p ]T [ v ]T
  U[] : {X Y : Con} {p : Tms X Y} → U n [ p ]T ≡ U n
  ʻEl[] : {X Y : Con} {u : Tm (suc n) Y (U n)} → {p : Tms X Y} → {z : Tm (suc n) X (U n)}
      → PathP (λ i → Tm (suc n) X (U[] {p = p} i)) (u [ box p ]-boxed) z
      → (El u) [ p ]T ≡ El z
  ʻPi[] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {p : Tms X Y} {z : Tm n (X , (A [ p ]T)) (A [ p ∘t π₁ idt ]T)}
      → PathP (λ i → Tm n (X , (A [ p ]T)) ([∘]T {A = A} {p = p} {v = π₁ idt} (~ i))) (π₂-boxed (box idt)) z
      → (Pi A B) [ p ]T ≡ Pi (A [ p ]T) (B [ p ∘t π₁ idt , z ]T)
  --L[] : {X Y : Con} {A : Ty n Y} {p : Tms X Y}
  --   → (L A) [ p ]T ≡ L (A [ p ]T)
  -- Type former equations
{--  U^η : {X : Con} → El (U^ {X} n) ≡ U n
  Pi^η : {X : Con} → (A : Tm (suc n) X (U n))
                   → (B : Tm (suc n) (X , El A) (U n))
                   → El (Pi^ A B) ≡ Pi (El A) (El B)
  L^η : {X : Con} → (A : Tm (suc n) X (U n))
                  → El (L^ A) ≡ L (El A)--}
  --mapType : A ≡ B → Tm n X A → Tm n X B
  -- Substitution equations
  id∘ : {X Y : Con} → {p : Tms X Y} → idt ∘t p ≡ p
  ∘id : {X Y : Con} → {p : Tms X Y} → p ∘t idt ≡ p
  ∘∘ : {X Y Z W : Con} → {p : Tms Z W} → {v : Tms Y Z} → {q : Tms X Y}
    → (p ∘t v) ∘t q ≡ p ∘t (v ∘t q)
  εη : {X : Con} → {p : Tms X ∅} → p ≡ ε
  π₁β : {X Y : Con} {A : Ty n Y} → {p : Tms X Y} → {u : Tm n X (A [ p ]T)}
      → π₁ (p , u) ≡ p
  πη : {X Y : Con} {A : Ty n Y} → {p : Tms X (Y , A)} → (π₁ p , π₂-boxed (box p)) ≡ p
  ʻ,∘ : {X Y Z : Con} {A : Ty n Z} → {p : Tms Y Z} → {v : Tms X Y} → {u : Tm n Y (A [ p ]T)} → {z : Tm n X (A [ p ∘t v ]T)}
    → PathP (λ i → Tm n X (sym ([∘]T {A = A} {p = p} {v = v}) i)) (u [ box v ]-boxed) z
    → ((p , u) ∘t v) ≡ ((p ∘t v) , z)
  -- Term equations
  ʻπ₂β : {X Y : Con} {A : Ty n Y} → {p : Tms X Y} → {u : Tm n X (A [ p ]T)} {z : Tm n X (A [ π₁ (p , u) ]T)}
     → PathP (λ i → Tm n X (A [ sym (π₁β {p = p} {u = u}) i ]T)) u z
     → π₂-boxed (box (p , u)) ≡ z
  β : {X : Con} {A : Ty n X} → {B : Ty n (X , A)} → {u : Tm n (X , A) B} → app (lam u) ≡ u
  η : {X : Con} {A : Ty n X} → {B : Ty n (X , A)} → {f : Tm n X (Pi A B)} → lam (app f) ≡ f
  ʻlam[] : {X Y : Con} {A : Ty n Y} → {B : Ty n (Y , A)} → {u : Tm n (Y , A) B} {p : Tms X Y} {z : Tm n X (Pi A B [ p ]T)}
          {w : Tm n (X , A [ p ]T) (A [ p ∘t π₁ idt ]T)}
       → (P : PathP (λ i → Tm n (X , A [ p ]T) (sym ([∘]T {A = A} {p = p} {v = π₁ idt}) i)) (π₂-boxed (box idt)) w)
       → PathP (λ i → Tm n X (ʻPi[] {A = A} {B = B} {p = p} P (~ i))) (lam (u [ box (p ∘t (π₁ idt) , w) ]-boxed)) z
       → (lam u) [ box p ]-boxed ≡ z
  -- Type former equations
{--  Pi^[] : {X Y : Con} {A : Tm (suc n) Y (U n)} {B : Tm (suc n) (Y , El A) (U n)} {p : Tms X Y}
       → (Pi^ A B) [ p ] ≡ subst (Tm (suc n) X) (sym U[]) (Pi^ (subst (Tm (suc n) X) U[] (A [ p ]))
                                                                (subst (Tm (suc n) _) U[] (B [ (p ∘t π₁ idt)
                                                                                               , subst (Tm n _) (sym [∘]T) ( (subst (λ i → Tm n (X , El (subst (Tm (suc n) X) U[] (A [ p ]))) (i [ π₁ idt ]T)) (sym El[]) (π₂ idt)) ) ])))
  L^[] : {X Y : Con} {A : Tm (suc n) Y (U n)} {p : Tms X Y}
       → (L^ A) [ p ] ≡ subst (Tm _ X) (sym U[]) (L^ (subst (Tm _ X) U[] (A [ p ]))) --}
  -- Collapse everything into sets
  isSetTy : {X : Con} → isSet (Ty n X)
  isSetTm : {X : Con} {A : Ty n X} → isSet (Tm n X A)
  isSetTms : {X Y : Con} → isSet (Tms X Y)
  -- Make 'El' injective.
  El-injective : {X : Con} {x y : Tm (suc n) X (U n)} → El x ≡ El y → x ≡ y

-- You thought we're going to go with the cosmetic damage?
pattern π₂ p = π₂-boxed (box p)
pattern _[_] u p = u [ box p ]-boxed

abstract
  El[] : {X Y : Con} {u : Tm (suc n) Y (U n)} → {p : Tms X Y}
       → (El u) [ p ]T ≡ El (subst (Tm (suc n) X) U[] (u [ p ]))
  El[] {n} {X} {Y} {u} {p} = ʻEl[] (subst-fill (Tm (suc n) X) U[] (u [ p ]))
  Pi[] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {p : Tms X Y}
  --      → PathP (λ i → Tm n (X , (A [ p ]T)) ([∘]T {A = A} {p = p} {v = π₁ idt} (~ i))) (π₂-boxed (box idt)) z
          → (Pi A B) [ p ]T ≡ Pi (A [ p ]T) (B [ p ∘t π₁ idt , subst (Tm _ _) (sym [∘]T) (π₂ idt) ]T)
  Pi[] {n} {X} {Y} {A} {B} {p} = ʻPi[] (subst-fill (Tm _ _) (sym [∘]T) (π₂ idt))
  ,∘ : {X Y Z : Con} {A : Ty n Z} → {p : Tms Y Z} → {v : Tms X Y} → {u : Tm n Y (A [ p ]T)}
     → ((p , u) ∘t v) ≡ ((p ∘t v) , subst (Tm n X) (sym [∘]T) (u [ v ]))
  ,∘ {n} {X} {Y} {Z} {A} {p} {v} {u} = ʻ,∘ (subst-fill (Tm _ _) (sym [∘]T) (u [ v ]))
  -- Term equations
  π₂β : {X Y : Con} {A : Ty n Y} → {p : Tms X Y} → {u : Tm n X (A [ p ]T)}
      → π₂-boxed (box (p , u)) ≡ subst (λ i → Tm n X (A [ i ]T)) (sym π₁β) u
  π₂β {n} {X} {Y} {A} {p} {u} = ʻπ₂β (subst-fill (λ i → Tm n X (A [ i ]T)) (sym π₁β) u)
  lam[] : {X Y : Con} {A : Ty n Y} → {B : Ty n (Y , A)} → {u : Tm n (Y , A) B} {p : Tms X Y}
        → (lam u) [ box p ]-boxed ≡ subst (Tm n X) (sym Pi[]) (lam (u [ (p ∘t (π₁ idt)
                                                                    , subst (Tm n (X , A [ p ]T)) (sym [∘]T) (π₂ idt)) ]))
  lam[] {n} {X} {Y} {A} {B} {u} {p} = ʻlam[]
                                      (subst-fill (Tm n (X , (A [ p ]T))) (sym [∘]T) (π₂ idt))
                                      (subst-fill (Tm n X) (sym Pi[]) (lam (u [ (p ∘t π₁ idt) , subst (Tm n (X , (A [ p ]T))) (sym [∘]T) (π₂ idt) ])))

-- return the universe level of the type, a convenience function.
universe : {X : Con} → Ty n X → ℕ
universe {n} _ = n

wk : {X : Con} {A : Ty n X} → Tms (X , A) X
wk = π₁ idt

vz : {X : Con} {A : Ty n X} → Tm n (X , A) (A [ wk ]T)
vz = π₂ idt

vs : {n m : ℕ} {X : Con} {A : Ty n X} {B : Ty m X} → Tm n X A → Tm n (X , B) (A [ wk ]T)
vs x = x [ wk ]

-- Lifting of a substitution by type
_↑_ : {X Y : Con} (p : Tms X Y) (A : Ty n Y) → Tms (X , A [ p ]T) (Y , A)
p ↑ A = (p ∘t π₁ idt) , subst (Tm _ _) (sym [∘]T) (π₂ idt)

-- Substitution of the last variable in the context
<_> : {X : Con} {A : Ty n X} → Tm n X A → Tms X (X , A)
< u > = idt , subst (Tm _ _) (sym [id]T) u

-- Application of terms
infixl 10 _$_
_$_ : {X : Con} {A : Ty n X} {B : Ty n (X , A)}
   → Tm n X (Pi A B) → (u : Tm n X A) → Tm n X (B [ < u > ]T)
f $ u = (app f) [ < u > ]

-- Context is a set
∅≢, : {X : Con} → {A : Ty n X} → (∅ ≡ (X , A)) → ⊥
∅≢, ∅≡, = transport (cong (λ{∅ → ⊤; (_ , _) → ⊥}) ∅≡,) tt

con-elim₁ : (X : Con) {Y : Con} {A : Ty n Y} → (X ≡ (Y , A)) → Con
con-elim₁ ∅ ∅≡, = absurd (∅≢, ∅≡,)
con-elim₁ (X , A) ,≡, = X

con-elim₀ : (X : Con) {Y : Con} {A : Ty n Y} → (X ≡ (Y , A)) → ℕ
con-elim₀ ∅ ∅≡, = absurd (∅≢, ∅≡,)
con-elim₀ (a , x) ,≡, = universe x

con-elim₂ : (X : Con) {Y : Con} {A : Ty n Y} → (X≡Y,A : X ≡ (Y , A)) → Ty (con-elim₀ X X≡Y,A) (con-elim₁ X X≡Y,A)
con-elim₂ ∅ ∅≡, = absurd (∅≢, ∅≡,)
con-elim₂ (X , A) ,≡, = A

con-injective₀ : {n m : ℕ} {X Y : Con} {A : Ty n X} {B : Ty m Y} → (p : Path Con (X , A) (Y , B)) → (n ≡ m)
con-injective₀ p i = con-elim₀ (p i) (λ j → p (i ∨ j))

con-injective₁ : {n m : ℕ} {X Y : Con} {A : Ty n X} {B : Ty m Y} → (p : Path Con (X , A) (Y , B)) → (X ≡ Y)
con-injective₁ p i = con-elim₁ (p i) (λ j → p (i ∨ j))

con-injective₂ : {n m : ℕ} {X Y : Con} {A : Ty n X} {B : Ty m Y} → (p : Path Con (X , A) (Y , B))
               → PathP (λ i → Ty (con-injective₀ p i) (con-injective₁ p i)) A B
con-injective₂ p i = con-elim₂ (p i) (λ j → p (i ∨ j))

con-theorem : (X : Con) → {Y : Con} → {A : Ty n Y} → (p : X ≡ (Y , A)) → (con-elim₁ X p , con-elim₂ X p) ≡ X
con-theorem ∅ ∅≡, = absurd (∅≢, ∅≡,)
con-theorem (X , A) X≡Y,A = refl

isSetCon : isSet Con
isSetCon ∅ ∅ ∅≡∅₁ ∅≡∅₂  = refl₁ ∙ sym refl₂
    where elim : (X : Con) → (p : X ≡ ∅) → X ≡ ∅
          elim ∅ ∅≡∅ = refl
          elim (X , x) ,≡∅ = absurd (∅≢, (sym ,≡∅))
          refl₁ : ∅≡∅₁ ≡ refl
          refl₁ i j = elim (∅≡∅₁ j) ((λ k → ∅≡∅₁ (j ∧ ~ k))) i
          refl₂ : ∅≡∅₂ ≡ refl
          refl₂ i j = elim (∅≡∅₂ j) ((λ k → ∅≡∅₂ (j ∧ ~ k))) i
isSetCon ∅ (Y , x) ∅≡, = absurd (∅≢, ∅≡,)
isSetCon (X , x) ∅ ,≡∅ = absurd (∅≢, (sym ,≡∅))
isSetCon (X , A) (Y , B) X,A≡Y,B₁ X,A≡Y,B₂ = thm₁ ∙ (λ i j → a i j , b i j ) ∙ sym thm₂
  where thm₁ : X,A≡Y,B₁ ≡ (λ i → _,_ {con-injective₀ X,A≡Y,B₁ i} (con-injective₁ X,A≡Y,B₁ i) (con-injective₂ X,A≡Y,B₁ i))
        thm₁ i j = (con-theorem (X,A≡Y,B₁ j) λ k → X,A≡Y,B₁ (j ∨ k)) (~ i)
        thm₂ : X,A≡Y,B₂ ≡ (λ i → _,_ {con-injective₀ X,A≡Y,B₂ i} (con-injective₁ X,A≡Y,B₂ i) (con-injective₂ X,A≡Y,B₂ i))
        thm₂ i j = (con-theorem (X,A≡Y,B₂ j) λ k → X,A≡Y,B₂ (j ∨ k)) (~ i)
        o : con-injective₀ X,A≡Y,B₁ ≡ con-injective₀ X,A≡Y,B₂
        o = isSetℕ (universe A) (universe B) (con-injective₀ X,A≡Y,B₁) (con-injective₀ X,A≡Y,B₂)
        a : (con-injective₁ X,A≡Y,B₁) ≡ (con-injective₁ X,A≡Y,B₂)
        a = isSetCon X Y (con-injective₁ X,A≡Y,B₁) (con-injective₁ X,A≡Y,B₂)
        b : PathP (λ i → PathP (λ j → Ty (o i j) (a i j)) A B) (con-injective₂ X,A≡Y,B₁) (con-injective₂ X,A≡Y,B₂)
        b i j = hcomp (λ k → λ{(i = i0) → transp (λ i → Ty (con-injective₀ X,A≡Y,B₁ j) (con-injective₁ X,A≡Y,B₁ j)) k (con-injective₂ X,A≡Y,B₁ j)
                               ;(i = i1) → transp (λ i → Ty (con-injective₀ X,A≡Y,B₂ j) (con-injective₁ X,A≡Y,B₂ j)) k (con-injective₂ X,A≡Y,B₂ j)
                               ;(j = i0) → transp (λ i → Ty (universe A) X) k A
                               ;(j = i1) → transp (λ i → Ty (universe B) Y) k B})
                      (isSetPath (λ k → isSetTy {X = a i k})
                                 (λ k → transp (λ z → Ty (o (i ∧ z) k) (a (i ∧ z) k)) i0 (con-injective₂ X,A≡Y,B₁ k))
                                 (λ k → transp (λ z → Ty (o (i ∨ ~ z) k) (a (i ∨ ~ z) k)) i0 (con-injective₂ X,A≡Y,B₂ k))
                                 i j)

{--
Con-elim : (P : Con → Set)
        → P ∅
        → ((X : Con) → (A : Ty X) → (P X) → P (X , A))
        → (X : Con) → P X
Con-elim P z s ∅ = z
Con-elim P z s (X , A) = s X A (Con-elim P z s X)
--}

instance
  isSetTy* : {X : Con} → IsSet* (Ty n X)
  IsSet*.isSet* isSetTy* = isSetTy

  isSetTms* : {X Y : Con} → IsSet* (Tms X Y)
  IsSet*.isSet* isSetTms* = isSetTms

  isSetTm* : {X : Con} {A : Ty n X} → IsSet* (Tm n X A)
  IsSet*.isSet* isSetTm* = isSetTm

  isSetCon* : IsSet* Con
  IsSet*.isSet* isSetCon* = isSetCon

  isSetConTy* : IsSet* (Σ Con (Ty n))
  IsSet*.isSet* isSetConTy* = isSetΣ isSetCon isSetTy
