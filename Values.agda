{-# OPTIONS --cubical #-}
module Values where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
open import Weakening

private variable n : ℕ

data Val (n : ℕ) (X : Con) : Ty n X → Set
data Sus (n : ℕ) (X : Con) : Ty n X → Set
data Env : Con → Con → Set

⌜_⌝Val : {X : Con} {A : Ty n X} → Val n X A → Tm n X A
⌜_⌝Sus : {X : Con} {A : Ty n X} → Sus n X A → Tm n X A
⌜_⌝Env : {X Y : Con} → Env X Y → Tms X Y

data Val n X where
  neu : {A : Ty n X} → Sus n X A → Val n X A
  lam : {Y : Con} → {A : Ty n Y} {B : Ty n (Y , A)}
      → Tm n (Y , A) B → (s : Env X Y) → Val n X ((Pi A B) [ ⌜ s ⌝Env ]T)
  veq : {A : Ty n X} {x y : Val n X A} → (⌜ x ⌝Val ≡ ⌜ y ⌝Val) → x ≡ y
  isSetVal : {A : Ty n X} → isSet (Val n X A)

data Sus n X where
  var : {A : Ty n X} → In n X A → Sus n X A
  app : {A : Ty n X} → {B : Ty n (X , A)}
      → (f : Sus n X (Pi A B))
      → (v : Val n X A)
      → Sus n X (B [ < ⌜ v ⌝Val > ]T)

data EnvR (n : ℕ) (X : Con) (Y : Con) (A : Ty n Y) : Set where
  _,_ : (p : Env X Y) → Val n X (A [ ⌜ p ⌝Env ]T) → EnvR n X Y A

SubEnv : Con → Con → Set
SubEnv X ∅ = ⊤
SubEnv X (Y , A) = EnvR (universe A) X Y A

data Env where -- to appease termination checker.
  env : {X Y : Con} → SubEnv X Y → Env X Y

⌜ neu x ⌝Val = ⌜ x ⌝Sus
⌜ lam u s ⌝Val = (lam u) [ ⌜ s ⌝Env ]
⌜ veq xy i ⌝Val = xy i
⌜ isSetVal x y xy1 xy2 i j ⌝Val = isSetTm _ _ (λ k → ⌜ xy1 k ⌝Val) (λ k → ⌜ xy2 k ⌝Val) i j

⌜ var x ⌝Sus = ⌜ x ⌝In
⌜ app a v ⌝Sus = ⌜ a ⌝Sus $ ⌜ v ⌝Val

⌜_⌝Env {Y = ∅} e = ε
⌜_⌝Env {Y = Y , A} (env (p , x)) = ⌜ p ⌝Env , ⌜ x ⌝Val

veqPath : {X : Con} {P : (i : I) → Ty n X} {x : Val n X (P i0)} {y : Val n X (P i1)}
        → PathP (λ i → Tm n X (P i)) ⌜ x ⌝Val ⌜ y ⌝Val
        → PathP (λ i → Val n X (P i)) x y
veqPath {X = X} {P} {x} {y} path i =  hcollapse x≡y (λ i → P i) i
  where x' : Val _ X (P i1)
        x' = subst (Val _ X) (λ i → P i) x
        xv≡yv : ⌜ x' ⌝Val ⟦ Tm _ X ⟧ ⌜ y ⌝Val
        xv≡yv = ⌜ x' ⌝Val
                 ⟮ ‼ dcong ⌜_⌝Val (sym (subst-fill (Val _ X) (λ i → P i) x)) ⟯
                 ⌜ x ⌝Val
                 ⟮ ‼ path ⟯
                 ⌜ y ⌝Val □
        x≡y : x ⟦ Val _ X ⟧ y
        x≡y = x
              ⟮ ‼ subst-fill (Val _ X) (λ i → P i) x ⟯
              x'
              ⟮ ‼ veq (hmerge xv≡yv) ⟯
              y □

eeq : {X Y : Con} {x y : Env X Y} → (⌜ x ⌝Env ≡ ⌜ y ⌝Env) → x ≡ y
eeq {X} {∅} {env tt} {env tt} xe≡ye = refl
eeq {X} {Y , A} {env (p , x)} {env (p' , x')} xe≡ye = λ i → env (eeq step1 i , veqPath {x = x} {y = x'} (hcollapse step2 (cong (λ x → A [ ⌜ x ⌝Env ]T) (eeq step1))) i)
  where step1 : ⌜ p ⌝Env ≡ ⌜ p' ⌝Env
        step1 = sym π₁β ∙ cong π₁ xe≡ye ∙ π₁β
        step2 : ⌜ x ⌝Val ⟦ Tm _ X ⟧ ⌜ x' ⌝Val
        step2 = hsym π₂βH ● ‼ dcong π₂ xe≡ye ● π₂βH

_[_]Val : {X Y : Con} {A : Ty n Y} → Val n Y A → (s : Wk X Y) → Val n X (A [ ⌜ s ⌝Wk ]T)
_[_]Sus : {X Y : Con} {A : Ty n Y} → Sus n Y A → (s : Wk X Y) → Sus n X (A [ ⌜ s ⌝Wk ]T)
_[_]Env : {X Y Z : Con} → Env Y Z → (s : Wk X Y) → Env X Z

⌜[]Val⌝ : {X Y : Con} {A : Ty n Y} → {v : Val n Y A} → {s : Wk X Y}
       → ⌜ v [ s ]Val ⌝Val ≡ ⌜ v ⌝Val [ ⌜ s ⌝Wk ]
⌜[]Sus⌝ : {X Y : Con} {A : Ty n Y} → {v : Sus n Y A} → {s : Wk X Y}
       → ⌜ v [ s ]Sus ⌝Sus ≡ ⌜ v ⌝Sus [ ⌜ s ⌝Wk ]
⌜[]Env⌝ : {X Y Z : Con} → {p : Env Y Z} → {s : Wk X Y}
       → ⌜ p [ s ]Env ⌝Env ≡ ⌜ p ⌝Env ∘t ⌜ s ⌝Wk

[[]Env] : {X Y Z : Con} {A : Ty n Z} {p : Env Y Z} {s : Wk X Y}
      → A [ ⌜ p [ s ]Env ⌝Env ]T ≡ A [ ⌜ p ⌝Env ]T [ ⌜ s ⌝Wk ]T
[[]Env] {X = X} {Y} {Z} {A} {p} {s}
  = A [ ⌜ p [ s ]Env ⌝Env ]T
    ≡⟨ cong (A [_]T) ⌜[]Env⌝ ⟩
    A [ ⌜ p ⌝Env ∘t ⌜ s ⌝Wk ]T
    ≡⟨ [∘]T ⟩
    (A [ ⌜ p ⌝Env ]T) [ ⌜ s ⌝Wk ]T ∎

[<>][] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {v : Val n Y A} {p : Wk X Y}
      → B [ ⌜ p ⌝Wk ↑ A ]T [ < ⌜ v [ p ]Val ⌝Val > ]T ≡ B [ < ⌜ v ⌝Val > ]T [ ⌜ p ⌝Wk ]T
[<>][] {X = X} {Y} {A} {B} {v} {p}
  = B [ ⌜ p ⌝Wk ↑ A ]T [ < ⌜ v [ p ]Val ⌝Val > ]T
  ≡⟨ sym [∘]T ⟩
  B [ (⌜ p ⌝Wk ↑ A) ∘t < ⌜ v [ p ]Val ⌝Val > ]T
  ≡⟨ cong (B [_]T) ↑∘<> ⟩
  B [ ⌜ p ⌝Wk , ⌜ v [ p ]Val ⌝Val ]T
  ≡⟨ cong (λ x → B [ _ , x ]T) (⌜[]Val⌝ {v = v}) ⟩
  (B [ ⌜ p ⌝Wk , (⌜ v ⌝Val [ ⌜ p ⌝Wk ]) ]T)
  ≡⟨ cong (B [_]T) (sym <>∘) ⟩
  B [ < ⌜ v ⌝Val > ∘t ⌜ p ⌝Wk ]T
  ≡⟨ [∘]T ⟩
  (B [ < ⌜ v ⌝Val > ]T) [ ⌜ p ⌝Wk ]T ∎

neu x [ s ]Val = neu (x [ s ]Sus)
lam x p [ s ]Val = tr (Val _ _) [[]Env] (lam x (p [ s ]Env))
veq {x = x} {y = y} p i [ s ]Val = veq {x = x [ s ]Val}
                                       {y = y [ s ]Val}
                                       (⌜[]Val⌝ {v = x} ∙ cong (λ x → x [ ⌜ s ⌝Wk ]) p ∙ sym (⌜[]Val⌝ {v = y}))
                                       i
isSetVal x y x≡y₁ x≡y₂ i j [ s ]Val = isSetVal _ _ (λ k → x≡y₁ k [ s ]Val)
                                                   (λ k → x≡y₂ k [ s ]Val) i j

var x [ s ]Sus = var (x [ s ]In)
app x v [ s ]Sus = tr (Sus _ _) ([<>][] {v = v}) (app (subst (Sus _ _) Pi[] (x [ s ]Sus)) (v [ s ]Val))

_[_]Env {Z = ∅} e s = env tt
_[_]Env {Z = Z , A} (env (p , x)) s = env (p [ s ]Env , tr (Val _ _) (sym [[]Env]) (x [ s ]Val))

abstract
  ⌜[]Val⌝ {X = X} {Y} {A} {neu x} {s} = ⌜[]Sus⌝ {v = x} {s = s}
  ⌜[]Val⌝ {X = X} {Y} {.(Pi _ _ [ ⌜ p ⌝Env ]T)} {lam u p} {s} = hmerge P
    where P : ⌜ tr (Val _ X) [[]Env] (lam u (p [ s ]Env)) ⌝Val
              ⟦ Tm _ X ⟧
              (lam u) [ ⌜ p ⌝Env ] [ ⌜ s ⌝Wk ]
          P = ⌜ tr (Val _ X) [[]Env] (lam u (p [ s ]Env)) ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (sym (trfill (Val _ X) [[]Env] (lam u (p [ s ]Env))))  ⟯
              lam u [ ⌜ p [ s ]Env ⌝Env ]
              ⟮ ‼ dcong (lam u [_]) ⌜[]Env⌝ ⟯
              lam u [ ⌜ p ⌝Env ∘t ⌜ s ⌝Wk ]
              ⟮ [∘] ⟯
              (lam u [ ⌜ p ⌝Env ]) [ ⌜ s ⌝Wk ] □
  ⌜[]Val⌝ {X = X} {Y} {A} {veq {x = x} {y = y} x≡y i} {s} j = outS (isSetFillSquare isSetTm p q (⌜[]Val⌝ {v = x} {s = s}) (⌜[]Val⌝ {v = y} {s = s}) j i)
    where p : ⌜ x [ s ]Val ⌝Val ≡ ⌜ y [ s ]Val ⌝Val
          p j = ⌜ veq {x = x [ s ]Val} {y = y [ s ]Val}
                      (⌜[]Val⌝ {v = x} ∙ cong (λ x → (x [ ⌜ s ⌝Wk ])) x≡y ∙ sym (⌜[]Val⌝ {v = y})) j ⌝Val
          q : (⌜ x ⌝Val [ ⌜ s ⌝Wk ]) ≡ (⌜ y ⌝Val [ ⌜ s ⌝Wk ])
          q j = ⌜ veq {x = x} {y = y} x≡y j ⌝Val [ ⌜ s ⌝Wk ]
  ⌜[]Val⌝ {X = X} {Y} {A} {isSetVal x y x≡y₁ x≡y₂ i j} {s} k = outS (isSetPartial isSetTm
                                                                                 (λ j → ⌜[]Val⌝ {v = x≡y₁ j} {s = s} k)
                                                                                 (λ j → ⌜[]Val⌝ {v = x≡y₂ j} {s = s} k)
                                                                                 (λ {(k = i0) → λ i j → ⌜ isSetVal _ _ (λ j → x≡y₁ j [ s ]Val)
                                                                                                                         (λ j → x≡y₂ j [ s ]Val) i j ⌝Val
                                                                                    ;(k = i1) → λ i j → ⌜ isSetVal _ _ x≡y₁ x≡y₂ i j ⌝Val [ ⌜ s ⌝Wk ]})) i j

  ⌜[]Sus⌝ {X = X} {Y} {A} {var x} {s} = ⌜[]In⌝ {x = x} {p = s}
  ⌜[]Sus⌝ {X = X} {Y} {.(_ [ < ⌜ x ⌝Val > ]T)} {app v x} {s} = hmerge P
    where P : ⌜ tr (Sus _ X) ([<>][] {v = x}) (app (subst (Sus _ X) Pi[] (v [ s ]Sus)) (x [ s ]Val)) ⌝Sus
              ⟦ Tm _ X ⟧
              (⌜ v ⌝Sus $ ⌜ x ⌝Val) [ ⌜ s ⌝Wk ]
          Q : ⌜ subst (Sus _ X) Pi[] (v [ s ]Sus) ⌝Sus
              ⟦ Tm _ X ⟧
              subst (Tm _ X) Pi[] (⌜ v [ s ]Sus ⌝Sus)
          P = ⌜ tr (Sus _ X) ([<>][] {v = x}) (app (subst (Sus _ X) Pi[] (v [ s ]Sus)) (x [ s ]Val)) ⌝Sus
              ⟮ ‼ dcong ⌜_⌝Sus (sym (trfill (Sus _ X) ([<>][] {v = x}) (app (subst (Sus _ X) Pi[] (v [ s ]Sus)) (x [ s ]Val)))) ⟯
              (⌜ subst (Sus _ X) Pi[] (v [ s ]Sus) ⌝Sus $ ⌜ x [ s ]Val ⌝Val)
              ⟮ ‼ dcong (λ i → ⌜ subst (Sus _ X) Pi[] (v [ s ]Sus) ⌝Sus $ i) (⌜[]Val⌝ {v = x}) ⟯
              (⌜ subst (Sus _ X) Pi[] (v [ s ]Sus) ⌝Sus $ (⌜ x ⌝Val [ ⌜ s ⌝Wk ]))
              ⟮ ‼ cong (λ i → i $ (⌜ x ⌝Val [ ⌜ s ⌝Wk ])) (hmerge Q) ⟯
              (subst (Tm _ X) Pi[] ⌜ v [ s ]Sus ⌝Sus $ (⌜ x ⌝Val [ ⌜ s ⌝Wk ]))
              ⟮ ‼ dcong (λ i → subst (Tm _ X) Pi[] i $ (⌜ x ⌝Val [ ⌜ s ⌝Wk ])) (⌜[]Sus⌝ {v = v}) ⟯
              (subst (Tm _ X) Pi[] (⌜ v ⌝Sus [ ⌜ s ⌝Wk ]) $ (⌜ x ⌝Val [ ⌜ s ⌝Wk ]))
              ⟮ hsym ($[] {f = ⌜ v ⌝Sus} {u = ⌜ x ⌝Val}) ⟯
              ((⌜ v ⌝Sus $ ⌜ x ⌝Val) [ ⌜ s ⌝Wk ]) □
          Q = ⌜ subst (Sus _ X) Pi[] (v [ s ]Sus) ⌝Sus
              ⟮ ‼ dcong ⌜_⌝Sus (sym (subst-filler (Sus _ X) Pi[] (v [ s ]Sus))) ⟯
              ⌜ v [ s ]Sus ⌝Sus
              ⟮ ‼ subst-filler (Tm _ X) Pi[] ⌜ v [ s ]Sus ⌝Sus ⟯
              subst (Tm _ X) Pi[] ⌜ v [ s ]Sus ⌝Sus □

  ⌜[]Env⌝ {X = X} {Y} {∅} {e} {s} = sym εη
  ⌜[]Env⌝ {X = X} {Y} {Z , A} {env (p , x)} {s} = hmerge P
    where P : (⌜ p [ s ]Env ⌝Env , ⌜ tr (Val _ X) (sym [[]Env]) (x [ s ]Val) ⌝Val)
              ⟦ Tms X ⟧
              (⌜ p ⌝Env , ⌜ x ⌝Val) ∘t ⌜ s ⌝Wk
          Q : ⌜ tr (Val _ X) (sym [[]Env]) (x [ s ]Val) ⌝Val
              ⟦ Tm _ X ⟧
              subst (Tm _ X) (sym [∘]T) (⌜ x ⌝Val [ ⌜ s ⌝Wk ])
          Q = ⌜ tr (Val _ X) (sym [[]Env]) (x [ s ]Val) ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (sym (trfill (Val _ X) (sym [[]Env]) (x [ s ]Val))) ⟯
              ⌜ x [ s ]Val ⌝Val
              ⟮ ‼ ⌜[]Val⌝ {v = x} ⟯
              ⌜ x ⌝Val [ ⌜ s ⌝Wk ]
              ⟮ ‼ subst-filler (Tm _ X) (sym [∘]T) (⌜ x ⌝Val [ ⌜ s ⌝Wk ]) ⟯
              subst (Tm _ X) (sym [∘]T) (⌜ x ⌝Val [ ⌜ s ⌝Wk ]) □ 
          P = (⌜ p [ s ]Env ⌝Env , ⌜ tr (Val _ X) (sym [[]Env]) (x [ s ]Val) ⌝Val)
              ⟮ (‼ λ i → ⌜[]Env⌝ {Y = Y} {p = p} {s = s} i , hcollapse Q (cong (_ [_]T) ⌜[]Env⌝) i) ⟯
              ((⌜ p ⌝Env ∘t ⌜ s ⌝Wk) , subst (Tm _ X) (sym [∘]T) (⌜ x ⌝Val [ ⌜ s ⌝Wk ]))
              ⟮ ‼ sym ,∘ ⟯
              (⌜ p ⌝Env , ⌜ x ⌝Val) ∘t ⌜ s ⌝Wk □

idenv : {X : Con} → Env X X
idenv≡ : {X : Con} → ⌜ idenv {X} ⌝Env ≡ idt

abstract
  ⌜id[weakener-idwk]⌝ : {X : Con} {A : Ty n X} → ⌜ idenv {X} [ weakener A idwk ]Env ⌝Env ≡ wk
  ⌜id[weakener-idwk]⌝ {X = X} {A}
    = ⌜ idenv {X} [ weakener A idwk ]Env ⌝Env
      ≡⟨ ⌜[]Env⌝ ⟩
      (⌜ idenv ⌝Env ∘t ⌜ weakener A idwk ⌝Wk)
      ≡⟨ cong (_∘t ⌜ weakener A idwk ⌝Wk) idenv≡ ⟩
      idt ∘t ⌜ weakener A idwk ⌝Wk
      ≡⟨ id∘ ⟩
      ⌜ weakener A idwk ⌝Wk
      ≡⟨ ⌜weakener⌝ ⟩
      ⌜ idwk ⌝Wk ∘t π₁ idt
      ≡⟨ cong (_∘t π₁ idt) ⌜idwk⌝ ⟩
      idt ∘t π₁ idt
      ≡⟨ id∘ ⟩
      π₁ idt ∎

  [⌜id[E]⌝] : {X : Con} {A : Ty n X} → A [ wk ]T ≡ A [ ⌜ idenv {X} [ weakener A idwk ]Env ⌝Env ]T
  [⌜id[E]⌝] {A = A} = cong (A [_]T) (sym ⌜id[weakener-idwk]⌝)
  
idenv {∅} = env tt
idenv {X , A} = env ((idenv {X} [ weakener A idwk ]Env) , tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)))

abstract
  idenv≡ {X = ∅} = sym εη
  idenv≡ {X = X , A} = hmerge P
    where p : ⌜ idenv {X} [ weakener A idwk ]Env ⌝Env ≡ wk
          p = ⌜id[weakener-idwk]⌝
          P : (⌜ idenv [ weakener A idwk ]Env ⌝Env , ⌜ tr (Val (universe A) (X , A)) [⌜id[E]⌝] (neu (var Zero)) ⌝Val)
              ⟦ Tms (X , A) ⟧
              idt
          Q : ⌜ tr (Val (universe A) (X , A)) [⌜id[E]⌝] (neu (var Zero)) ⌝Val
              ⟦ Tm _ (X , A) ⟧
              vz
          P = (⌜ idenv {X} [ weakener A idwk ]Env ⌝Env , ⌜ tr (Val (universe A) (X , A)) [⌜id[E]⌝] (neu (var Zero)) ⌝Val)
              ⟮ ‼ dcong₂ term._,_ p (hcollapse Q (cong (A [_]T) p)) ⟯
              (π₁ idt , π₂ idt)
              ⟮ ‼ πη ⟯
              idt □
          Q = ⌜ tr (Val (universe A) (X , A)) [⌜id[E]⌝] (neu (var Zero)) ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (sym (trfill (Val _ _) [⌜id[E]⌝] (neu (var Zero)))) ⟯
              vz □

abstract
  [○]Val : {X Y Z : Con} {A : Ty n Z} {v : Val n Z A} {s : Wk Y Z} {a : Wk X Y}
         → v [ s ○ a ]Val ≡ subst (Val _ _) ○-lemma (v [ s ]Val [ a ]Val)
  [○]Val {n} {X} {Y} {Z} {A} {v} {s} {a} = veq (hmerge P)
    where P : ⌜ v [ s ○ a ]Val ⌝Val
              ⟦ Tm _ _ ⟧
              ⌜ subst (Val n X) ○-lemma ((v [ s ]Val) [ a ]Val) ⌝Val
          P = ⌜ v [ s ○ a ]Val ⌝Val
              ⟮ ‼ ⌜[]Val⌝ {v = v} ⟯
              ⌜ v ⌝Val [ ⌜ s ○ a ⌝Wk ]
              ⟮ ‼ dcong (⌜ v ⌝Val [_]) ⌜○⌝ ⟯
              ⌜ v ⌝Val [ ⌜ s ⌝Wk ∘t ⌜ a ⌝Wk ]
              ⟮ [∘] ⟯
              ⌜ v ⌝Val [ ⌜ s ⌝Wk ] [ ⌜ a ⌝Wk ]
              ⟮ ‼ dcong (_[ ⌜ a ⌝Wk ]) (sym (⌜[]Val⌝ {v = v})) ⟯
              ⌜ v [ s ]Val ⌝Val [ ⌜ a ⌝Wk ]
              ⟮ ‼ sym (⌜[]Val⌝ {v = v [ s ]Val}) ⟯
              ⌜ v [ s ]Val [ a ]Val ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (subst-filler (Val n X) ○-lemma (v [ s ]Val [ a ]Val)) ⟯
              ⌜ subst (Val n X) ○-lemma ((v [ s ]Val) [ a ]Val) ⌝Val □
