{-# OPTIONS --cubical #-}
module EvalSpec where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax
open import Lemmas
open import Weakening
open import Values
open import NormalForm
open import TermInfo

private variable n : ℕ

data eval : {X Y : Con} {A : Ty n Y} {B : Ty n X} → Tm n Y A → Env X Y → Val n X B → Set
data evals : {X Y Z : Con} → Tms Y Z → Env X Y → Env X Z → Set
data apply : {X : Con} → {A : Ty n X} {B : Ty n (X , A)} {C : Ty n X} → Val n X (Pi A B) → Val n X A → Val n X C → Set

eval≡ : {X Y : Con} {A : Ty n Y} {B : Ty n X} → {u : Tm n Y A} → {p : Env X Y} → {v : Val n X B}
      → eval u p v
      → ⌜ v ⌝Val ⟦ Tm _ X ⟧ u [ ⌜ p ⌝Env ]
evals≡ : {X Y Z : Con} → {s : Tms Y Z} → {p : Env X Y} → {w : Env X Z}
       → evals s p w
       → ⌜ w ⌝Env ≡ s ∘t ⌜ p ⌝Env
apply≡ : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {C : Ty n X} → {f : Val n X (Pi A B)} → {v : Val n X A} → {w : Val n X C}
       → apply f v w
       → (⌜ f ⌝Val $ ⌜ v ⌝Val) ⟦ Tm _ X ⟧ ⌜ w ⌝Val
       
abstract
  evals,-aux : {X Y Z : Con} {A : Ty n Z} {B : Ty n X} {s : Tms Y Z} {u : Tm n Y (A [ s ]T)}
             → {p : Env X Y} {sp : Env X Z} {up : Val n X B}
             → evals s p sp → eval u p up → B ≡ A [ ⌜ sp ⌝Env ]T
  evals,-aux {A = A} {B} {s} {u} {p} {sp} es eu
    = B
      ≡⟨ type (eval≡ eu) ⟩
      (A [ s ]T) [ ⌜ p ⌝Env ]T
      ≡⟨ sym [∘]T ⟩
      A [ s ∘t ⌜ p ⌝Env ]T
      ≡⟨ sym (cong (A [_]T) (evals≡ es)) ⟩
      A [ ⌜ sp ⌝Env ]T ∎

data eval where
  evalπ₂ : {X Y Z : Con} {A : Ty n Y} {s : Tms Z (Y , A)} {p : Env X Z} {w : Env X Y} {v : Val n X (A [ ⌜ w ⌝Env ]T)}
         → evals s p (env (w , v)) → eval (π₂ s) p v
  eval[] : {X Y Z : Con} {A : Ty n Z} {B : Ty n X} {s : Tms Y Z} {p : Env X Y} {w : Env X Z} {u : Tm n Z A} {v : Val n X B}
         → evals s p w → eval u w v → eval (u [ s ]) p v
  evallam : {X Y : Con} {A : Ty n X} {B : Ty n (X , A)} {u : Tm n (X , A) B} {p : Env Y X}
         → eval (lam u) p (lam u p)
  evalapp : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)}
            {f : Tm n Y (Pi A B)} {p : Env X Y}
            {C : Ty n (X , A [ ⌜ p ⌝Env ]T)} {D : Ty n X}
            {g : Val n X (Pi (A [ ⌜ p ⌝Env ]T) C)} {v : Val n X (A [ ⌜ p ⌝Env ]T)} {w : Val n X D}
         → eval f p g → apply g v w → eval (app f) (env (p , v)) w
  isPropEval : {X Y : Con} {A : Ty n Y} {B : Ty n X} {u : Tm n Y A} {p : Env X Y} {v : Val n X B} → isProp (eval u p v)

data evals where
  evalsid : {X Y : Con} {p : Env X Y}
         → evals idt p p
  evals∘ : {X Y Z W : Con} {v : Tms Y Z} {p : Env X Y} {w : Env X Z} {s : Tms Z W} {e : Env X W}
         → evals v p w → evals s w e → evals (s ∘t v) p e
  evalsε : {X Y : Con} {p : Env X Y}
         → evals ε p (env tt)
  evals, : {X Y Z : Con} {A : Ty n Z} {B : Ty n X} {s : Tms Y Z} {p : Env X Y} {w : Env X Z} {u : Tm n Y (A [ s ]T)} {v : Val n X B}
         → (es : evals s p w) → (eu : eval u p v) → evals (s , u) p (env (w , tr (Val _ X) (evals,-aux es eu) v))
  evalsπ₁ : {X Y Z : Con} {A : Ty n Z} {s : Tms Y (Z , A)} {p : Env X Y} {w : Env X Z} {v : Val n X (A [ ⌜ w ⌝Env ]T)}
         → evals s p (env (w , v)) → evals (π₁ s) p w
  isPropEvals : {X Y Z : Con} {p : Tms Y Z} {s : Env X Y} {v : Env X Z} → isProp (evals p s v)

data apply where
  lam : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {C : Ty n X}
        {u : Tm n (Y , A) B} {p : Env X Y} {v : Val n X (A [ ⌜ p ⌝Env ]T)} {w : Val n X C}
      → eval u (env (p , v)) w → apply (subst (Val _ X) Pi[] (lam u p)) v w
  neu : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {sv : Sus n X (Pi A B)} {v : Val n X A}
      → apply (neu sv) v (neu (app sv v))
  isPropApply : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {C : Ty n X} → {f : Val n X (Pi A B)} → {x : Val n X A} → {v : Val n X C}
             → isProp (apply f x v)

abstract
  eval≡ (evalπ₂ {n} {X} {Y} {Z} {A} {s} {p} {w} {v} es)
    = ⌜ v ⌝Val
      ⟮ hsym π₂βH ⟯
      (π₂ (⌜ w ⌝Env , ⌜ v ⌝Val))
      ⟮ ‼ cong π₂ (evals≡ es) ⟯
      π₂ (s ∘t ⌜ p ⌝Env)
      ⟮ π₂∘ ⟯
      π₂ s [ ⌜ p ⌝Env ] □
  eval≡ (eval[] {n} {X} {Y} {Z} {A} {B} {s} {p} {w} {u} {v} es eu)
    = ⌜ v ⌝Val
      ⟮ eval≡ eu ⟯
      u [ ⌜ w ⌝Env ]
      ⟮ ‼ cong (u [_]) (evals≡ es) ⟯
      u [ s ∘t ⌜ p ⌝Env ]
      ⟮ [∘] ⟯
      (u [ s ]) [ ⌜ p ⌝Env ] □
  eval≡ (evallam {n} {X} {Y} {A} {B} {u} {p})
    = lam u [ ⌜ p ⌝Env ] □
  eval≡ (evalapp {n} {X} {Y} {A} {B} {f} {p} {C} {D} {g} {v} {w} ef ag)
    = ⌜ w ⌝Val
      ⟮ hsym (apply≡ ag) ⟯
      (⌜ g ⌝Val $ ⌜ v ⌝Val)
      ⟮ ‼ dcong (_$ ⌜ v ⌝Val) (hcollapse P (cong (Pi (A [ ⌜ p ⌝Env ]T)) (hmerge Q))) ⟯
      (subst (Tm n X) Pi[] (f [ ⌜ p ⌝Env ]) $ ⌜ v ⌝Val)
      ⟮ ‼ dcong₂ (λ x y → (subst (Tm n X) Pi[] (f [ x ])) $ y) (sym π₁β) (hcollapse (hsym π₂βH) (cong (A [_]T) (sym π₁β))) ⟯
      (subst (Tm n X) Pi[] (f [ π₁ (⌜ p ⌝Env , ⌜ v ⌝Val) ]) $ π₂ (⌜ p ⌝Env , ⌜ v ⌝Val))
      ⟮ hsym app[] ⟯
      app f [ ⌜ p ⌝Env , ⌜ v ⌝Val ] □
      where P : ⌜ g ⌝Val
                ⟦ Tm n X ⟧
                (subst (Tm n X) Pi[] (f [ ⌜ p ⌝Env ]))
            P = ⟨ Tm n X (Pi (A [ ⌜ p ⌝Env ]T) C) ⟩ ⌜ g ⌝Val
                ⟮ eval≡ ef ⟯
                f [ ⌜ p ⌝Env ]
                ⟮ ‼ subst-filler (Tm n X) Pi[] (f [ ⌜ p ⌝Env ]) ⟯
                ⟨ Tm n X (Pi (A [ ⌜ p ⌝Env ]T) (B [ (⌜ p ⌝Env ∘t π₁ idt)
                                                 , subst (Tm n (X , (A [ ⌜ p ⌝Env ]T)))
                                                         (sym [∘]T)
                                                         (π₂ idt) ]T)) ⟩
                (subst (Tm n X) Pi[] (f [ ⌜ p ⌝Env ])) □
            Q : C ⟦ Ty n ⟧ B [ ⌜ p ⌝Env ↑ A ]T
            Q = ‼ cong snd (just-injective (cong domains (type (eval≡ ef))))
            
      
  eval≡ (isPropEval {n} {X} {Y} {A} {B} {u} {p} {v} x y i)
    = hisSet isSetTy isSetTm (eval≡ x) (eval≡ y) i

  evals≡ (evalsid {X} {Y} {p})
    = sym id∘
  evals≡ (evals∘ {X} {Y} {Z} {W} {v} {p} {w} {s} {e} ev es)
    = ⌜ e ⌝Env
      ≡⟨ evals≡ es ⟩
      s ∘t ⌜ w ⌝Env
      ≡⟨ cong (s ∘t_) (evals≡ ev) ⟩
      (s ∘t (v ∘t ⌜ p ⌝Env))
      ≡⟨ sym ∘∘ ⟩
      ((s ∘t v) ∘t ⌜ p ⌝Env) ∎
  evals≡ (evalsε {X} {Y} {p})
    = sym εη
  evals≡ (evals, {n} {X} {Y} {Z} {A} {B} {s} {p} {w} {u} {v} es eu)
    = (⌜ w ⌝Env , ⌜ tr (Val (universe A) X) (evals,-aux es eu) v ⌝Val)
      ≡⟨ dcong₂ (term._,_) (evals≡ es) (hcollapse P (cong (A [_]T) (evals≡ es))) ⟩
      ((s ∘t ⌜ p ⌝Env) , subst (Tm (universe A) X) (sym [∘]T) (u [ ⌜ p ⌝Env ]))
       ≡⟨ sym ,∘ ⟩
       ((s , u) ∘t ⌜ p ⌝Env) ∎
    where P : ⌜ tr (Val (universe A) X) (evals,-aux es eu) v ⌝Val
              ⟦ Tm n X ⟧
              subst (Tm (universe A) X) (sym [∘]T) (u [ ⌜ p ⌝Env ])
          P = ⌜ tr (Val (universe A) X) (evals,-aux es eu) v ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (sym (trfill (Val (universe A) X) (evals,-aux es eu) v)) ⟯
              ⌜ v ⌝Val
              ⟮ eval≡ eu ⟯
              (u [ ⌜ p ⌝Env ])
              ⟮ ‼ subst-filler (Tm (universe A) X) (sym [∘]T) (u [ ⌜ p ⌝Env ]) ⟯
              (subst (Tm (universe A) X) (sym [∘]T) (u [ ⌜ p ⌝Env ])) □
  evals≡ (evalsπ₁ {n} {X} {Y} {Z} {A} {s} {p} {w} {v} es)
    = ⌜ w ⌝Env
      ≡⟨ sym π₁β ⟩
      π₁ (⌜ w ⌝Env , ⌜ v ⌝Val)
      ≡⟨ cong π₁ (evals≡ es) ⟩
      π₁ (s ∘t ⌜ p ⌝Env)
      ≡⟨ π₁∘ ⟩
      (π₁ s ∘t ⌜ p ⌝Env) ∎
  evals≡ (isPropEvals {X} {Y} {Z} {p} {s} {v} x y i)
    = isSetTms _ _ (evals≡ x) (evals≡ y) i

  apply≡ (lam {n} {X} {Y} {A} {B} {C} {u} {p} {v} {w} eu)
    = (⌜ subst (Val n X) Pi[] (lam u p) ⌝Val $ ⌜ v ⌝Val)
      ⟮ ‼ cong (λ i → i $ ⌜ v ⌝Val) (hmerge P) ⟯
      (subst (Tm n X) Pi[] (lam u [ ⌜ p ⌝Env ]) $ ⌜ v ⌝Val)
      ⟮ clos[] ⟯
      (u [ ⌜ p ⌝Env , ⌜ v ⌝Val ])
      ⟮ hsym (eval≡ eu) ⟯
      ⌜ w ⌝Val □
    where P : ⌜ subst (Val n X) Pi[] (lam u p) ⌝Val
              ⟦ Tm n X ⟧
              subst (Tm n X) Pi[] ⌜ lam u p ⌝Val
          P = ⌜ subst (Val n X) Pi[] (lam u p) ⌝Val
               ⟮ ‼ dcong ⌜_⌝Val (sym (subst-filler (Val n X) Pi[] (lam u p))) ⟯
               lam u [ ⌜ p ⌝Env ]
               ⟮ ‼ subst-filler (Tm n X) Pi[] (lam u [ ⌜ p ⌝Env ]) ⟯
               (subst (Tm n X) Pi[] (lam u [ ⌜ p ⌝Env ])) □
  apply≡ (neu {n} {X} {A} {B} {sv} {v})
    = (⌜ sv ⌝Sus $ ⌜ v ⌝Val) □
  apply≡ (isPropApply {n} {X} {A} {B} {C} {f} {x} {v} a₁ a₂ i)
    = hisSet isSetTy isSetTm (apply≡ a₁) (apply≡ a₂) i

evalSound : {X Y : Con} {A : Ty n Y} {B B' : Ty n X} {u : Tm n Y A} {p : Env X Y} {v : Val n X B} {w : Val n X B'}
          → eval u p v → eval u p w
          → v ⟦ Val _ _ ⟧ w
evalsSound : {X Y Z : Con} {s : Tms Y Z} {p : Env X Y} {w v : Env X Z}
           → evals s p w → evals s p v
           → w ≡ v
applySound : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {C C' : Ty n X} {f : Val n X (Pi A B)} {v : Val n X A} {w : Val n X C} {z : Val n X C'}
           → apply f v w → apply f v z
           → w ⟦ Val _ _ ⟧ z
evalSound {v = v} {w = w} e1 e2 = ‼ veqPath (hcollapse P (type P))
  where P : ⌜ v ⌝Val ⟦ Tm _ _ ⟧ ⌜ w ⌝Val
        P = eval≡ e1 ● hsym (eval≡ e2)
evalsSound e1 e2 = eeq (evals≡ e1 ∙ sym (evals≡ e2))
applySound {w = w} {z = z} a1 a2 = ‼ veqPath (hcollapse P (type P))
  where P : ⌜ w ⌝Val ⟦ Tm _ _ ⟧ ⌜ z ⌝Val
        P = hsym (apply≡ a1) ● apply≡ a2

data quot : {n : ℕ} {X : Con} {A : Ty n X} → Val n X A → Nf n X A → Set
data quots : {n : ℕ} {X : Con} {A : Ty n X} → Sus n X A → Nu n X A → Set

quot≡ : {X : Con} {A : Ty n X} {v : Val n X A} {w : Nf n X A}
      → quot v w → ⌜ v ⌝Val ≡ ⌜ w ⌝Nf
quots≡ : {X : Con} {A : Ty n X} {m : Sus n X A} {w : Nu n X A}
      → quots m w → ⌜ m ⌝Sus ≡ ⌜ w ⌝Nu

data quot where
  quotU : {X : Con} {v : Sus (suc n) X (U n)} {w : Nu (suc n) X (U n)}
       → quots v w → quot (neu v) (neuU w)
  quotEl : {X : Con} {u : Tm (suc n) X (U n)} {v : Sus n X (El u)} {w : Nu n X (El u)}
       → quots v w → quot (neu v) (neuEl w)
--  quotL : {X : Con} {A : Ty n X} {v : Sus (suc n) X (L A)} {w : Nu (suc n) X (L A)}
--       → quots v w → quot (neu v) (neuL w)
  quotPi : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {f : Val n X (Pi A B)} {v : Val n (X , A) B} {w : Nf n (X , A) B}
       → apply (subst (Val _ _) Pi[] (f [ weakener A idwk ]Val))
                (tr (Val _ _) idwk-lemma (neu (var Zero)))
                v
       → quot v w → quot f (lam w)
  isPropQuot : {X : Con} {A : Ty n X} {v : Val n X A} → {w : Nf n X A} → isProp (quot v w)

data quots where
  quotsvar : {X : Con} {A : Ty n X} {x : In n X A} → quots (var x) (var x)
  quotsapp : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {f : Sus n X (Pi A B)}
             {m : Nu n X (Pi A B)} {v : Val n X A} {w : Nf n X A}
           → quots f m → (qv : quot v w) → quots (app f v) (tr (λ x → Nu n X (B [ < x > ]T)) (sym (quot≡ qv)) (app m w))
  isPropQuots : {X : Con} {A : Ty n X} {v : Sus n X A} → {w : Nu n X A} → isProp (quots v w)

quot≡ (quotU qv) = quots≡ qv
quot≡ (quotEl qv) = quots≡ qv
--quot≡ (quotL qv) = quots≡ qv
quot≡ (quotPi {X = X} {A} {B} {f} {v} {w} af qv)
  = hmerge P
  where P : ⌜ f ⌝Val ⟦ Tm _ X ⟧ lam ⌜ w ⌝Nf
        R : π₁ idt ≡ ⌜ weakener A idwk ⌝Wk
        Q : subst (Tm _ (X , A)) Pi[] (⌜ f ⌝Val [ π₁ idt ])
            ⟦ Tm _ (X , A) ⟧
            ⌜ subst (Val _ (X , A)) Pi[] (f [ weakener A idwk ]Val) ⌝Val
        S : π₂ idt
            ⟦ Tm _ (X , A) ⟧
            ⌜ tr (Val _ (X , A)) idwk-lemma (neu (var Zero)) ⌝Val
        P = ⌜ f ⌝Val
            ⟮ ‼ sym η ⟯
            lam (app ⌜ f ⌝Val)
            ⟮ hcong term.lam (hsym [id]) ⟯
            lam (app ⌜ f ⌝Val [ idt ])
            ⟮ hcong term.lam app[] ⟯
            (lam (subst (Tm _ (X , A)) Pi[] (⌜ f ⌝Val [ π₁ idt ]) $ π₂ idt))
            ⟮ ‼ dcong₂ (λ x y → term.lam (x $ y)) (hcollapse Q (cong (λ i → Pi (A [ i ]T) (B [ (i ∘t π₁ idt) , subst (Tm _ ((X , A) , (A [ i ]T))) (sym [∘]T) (π₂ idt) ]T)) R))
                                                   (hcollapse S (cong (A [_]T) R)) ⟯
            (lam (⌜ subst (Val _ (X , A)) Pi[] (f [ weakener A idwk ]Val) ⌝Val $ ⌜ tr (Val _ (X , A)) idwk-lemma (neu (var Zero)) ⌝Val))
            ⟮ hcong term.lam (apply≡ af) ⟯
            lam ⌜ v ⌝Val
            ⟮ ‼ cong term.lam (quot≡ qv) ⟯
            lam ⌜ w ⌝Nf □
        R = π₁ idt
            ≡⟨ sym id∘ ⟩
            (idt ∘t π₁ idt)
            ≡⟨ cong (_∘t π₁ idt) (sym ⌜idwk⌝) ⟩
            ⌜ idwk ⌝Wk ∘t π₁ idt
            ≡⟨ sym ⌜weakener⌝ ⟩
            ⌜ weakener A idwk ⌝Wk ∎
        Q = subst (Tm _ (X , A)) Pi[] (⌜ f ⌝Val [ π₁ idt ])
            ⟮ ‼ sym (subst-filler (Tm _ (X , A)) Pi[] (⌜ f ⌝Val [ π₁ idt ])) ⟯
            (⌜ f ⌝Val [ π₁ idt ])
            ⟮ ‼ cong (⌜ f ⌝Val [_]) R ⟯
            (⌜ f ⌝Val [ ⌜ weakener A idwk ⌝Wk ])
            ⟮ ‼ sym (⌜[]Val⌝ {v = f}) ⟯
            ⌜ f [ weakener A idwk ]Val ⌝Val
            ⟮ ‼ dcong ⌜_⌝Val (subst-filler (Val _ (X , A)) Pi[] (f [ weakener A idwk ]Val)) ⟯
            ⌜ subst (Val _ (X , A)) Pi[] (f [ weakener A idwk ]Val) ⌝Val □
        S = π₂ idt
            ⟮ ‼ dcong ⌜_⌝Val (trfill (Val _ (X , A)) idwk-lemma (neu (var Zero))) ⟯
            ⌜ tr (Val _ (X , A)) idwk-lemma (neu (var Zero)) ⌝Val □

quot≡ (isPropQuot x y i) = isSetTm _ _ (quot≡ x) (quot≡ y) i

quots≡ quotsvar = refl
quots≡ (quotsapp {X = X} {A} {B} {f} {m} {v} {w} qf qv)
  = hmerge P
  where P : (⌜ f ⌝Sus $ ⌜ v ⌝Val)
            ⟦ Tm _ X ⟧
            ⌜ tr (λ x → Nu _ X (B [ < x > ]T)) (sym (quot≡ qv)) (app m w) ⌝Nu
        P = (⌜ f ⌝Sus $ ⌜ v ⌝Val)
            ⟮ ‼ cong (_$ ⌜ v ⌝Val) (quots≡ qf) ⟯
            (⌜ m ⌝Nu $ ⌜ v ⌝Val)
            ⟮ ‼ dcong (⌜ m ⌝Nu $_) (quot≡ qv) ⟯
            (⌜ m ⌝Nu $ ⌜ w ⌝Nf)
            ⟮ ‼ dcong ⌜_⌝Nu (trfill (λ x → Nu _ X (B [ < x > ]T)) (sym (quot≡ qv)) (app m w)) ⟯
            ⌜ tr (λ x → Nu _ X (B [ < x > ]T)) (sym (quot≡ qv)) (app m w) ⌝Nu □
quots≡ (isPropQuots x y i) = isSetTm _ _ (quots≡ x) (quots≡ y) i

quot-sound : {X : Con} {A : Ty n X} {v : Val n X A} {w z : Nf n X A}
   → quot v w → quot v z → w ≡ z
quot-sound p q = nfeq (sym (quot≡ p) ∙ quot≡ q)

--quots-sound : {X : Con} {A : Ty n X} {v : Sus n X A} {w z : Nu n X A}
--   → quots v w → quots v z → w ≡ z
--quots-sound p q = {!!}


_[_]eval : {X Y Z : Con} {A : Ty n Z} {B : Ty n Y}
           {u : Tm n Z A} {p : Env Y Z} {w : Val n Y B}
         → eval u p w → (s : Wk X Y) → eval u (p [ s ]Env) (w [ s ]Val) 
_[_]evals : {X Y Z W : Con} {q : Tms Z W} {p : Env Y Z} {e : Env Y W}
         → evals q p e → (s : Wk X Y) → evals q (p [ s ]Env) (e [ s ]Env)
_[_]apply : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {C : Ty n Y}
         → {f : Val n Y (Pi A B)} {v : Val n Y A} {w : Val n Y C}
         → apply f v w → (s : Wk X Y) → apply (subst (Val n X) Pi[] (f [ s ]Val)) (v [ s ]Val) (w [ s ]Val)

evalπ₂ {X = X} {Y} {Z} {A} {z} {p} {w} {v} ez [ s ]eval = transport (λ i → eval (π₂ z)
                                                                              (p [ s ]Env)
                                                                              (trfill (Val _ _) (sym [[]Env]) (v [ s ]Val) (~ i))) π₂+
  where π₂+ : eval (π₂ z) (p [ s ]Env) (tr (Val _ _) (sym [[]Env]) (v [ s ]Val))
        π₂+ = evalπ₂ (ez [ s ]evals)
eval[] {X = X} {Y} {Z} {A} {B} {z} {p} {w} {u} {v} ez eu [ s ]eval = eval[] (ez [ s ]evals) (eu [ s ]eval)
evallam {X = X} {Y} {A} {B} {u} {p} [ s ]eval = transport (λ i → eval (lam u) (p [ s ]Env)
                                                                       (trfill (Val _ _) [[]Env] (lam u (p [ s ]Env)) i)) lam+
  where lam+ : eval (lam u) (p [ s ]Env) (lam u (p [ s ]Env))
        lam+ = evallam {u = u} {p = p [ s ]Env}
_[_]eval {X = X'} (evalapp {X = X} {Y} {A} {B} {f} {p} {C} {D} {g} {v} {w} ef ag) s = evalapp ef+' ag+'
  where p+ = p [ s ]Env
        P : A [ ⌜ p ⌝Env ]T [ ⌜ s ⌝Wk ]T ≡ A [ ⌜ p+ ⌝Env ]T
        P = sym [[]Env]
        v+ = v [ s ]Val
        v+' = tr (Val _ _) P v+
        v+≡v+' = trfill (Val _ _) P v+
        C+ = C [ ⌜ s ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T
        C+' = tr (λ x → Ty (universe A) (X' , x)) P C+
        C+≡C+' = trfill (λ x → Ty (universe A) (X' , x)) P C+
        Q : I → Ty _ _
        Q i = Pi (P i) (C+≡C+' i)
        g+ = g [ s ]Val
        g+' = subst (Val _ _) Pi[] g+
        g+'' = tr (Val _ _) (λ i → Q i) g+'
        g+≡g+'' : g+ ⟦ Val _ _ ⟧ g+''
        g+≡g+'' = g+
                  ⟮ ‼ subst-filler (Val _ _) Pi[] g+ ⟯
                  g+'
                  ⟮ ‼ trfill (Val _ _) (λ i → Q i) g+' ⟯
                  g+'' □
        w+ = w [ s ]Val
        ef+ : eval f p+ g+
        ef+ = ef [ s ]eval
        ef+' : eval f p+ g+''
        ef+' = transport (λ i → eval f p+ (hcollapse g+≡g+'' (Pi[] ∙ (λ i → Q i)) i)) ef+
        ag+ : apply g+' v+ w+
        ag+ = ag [ s ]apply
        ag+' : apply g+'' v+' w+
        ag+' = transport (λ i → apply (trfill (Val _ _) (λ i → Q i) g+' i) (v+≡v+' i) w+) ag+
isPropEval x y i [ s ]eval = isPropEval (x [ s ]eval) (y [ s ]eval) i

evalsid [ s ]evals = evalsid
evals∘ {X = X} {Y} {Z} {W} {v} {p} {w} {z} {u} ev ez [ s ]evals = evals∘ (ev [ s ]evals) (ez [ s ]evals)
evalsε [ s ]evals = evalsε
evals, {X = X} {Y} {Z} {A} {B} {z} {p} {w} {u} {v}  ez eu [ s ]evals
  = transport (λ i → evals (z , u) (p [ s ]Env) (env ((w [ s ]Env) , hmerge m i))) ,+
  where ez+ : evals z (p [ s ]Env) (w [ s ]Env)
        ez+ = ez [ s ]evals
        eu+ : eval u (p [ s ]Env) (v [ s ]Val)
        eu+ = eu [ s ]eval
        m : tr (Val _ _) (evals,-aux ez+ eu+) (v [ s ]Val)
            ⟦ Val _ _ ⟧
            tr (Val _ _) (sym [[]Env]) (tr (Val _ _) (evals,-aux ez eu) v [ s ]Val)
        m = tr (Val _ _) (evals,-aux ez+ eu+) (v [ s ]Val)
            ⟮ ‼ sym (trfill (Val _ _) (evals,-aux ez+ eu+) (v [ s ]Val)) ⟯
            v [ s ]Val
            ⟮ ‼ dcong (_[ s ]Val) (trfill (Val _ _) (evals,-aux ez eu) v) ⟯
            tr (Val _ _) (evals,-aux ez eu) v [ s ]Val
            ⟮ ‼ trfill (Val _ _) (sym [[]Env]) (tr (Val _ _) (evals,-aux ez eu) v [ s ]Val) ⟯
            tr (Val _ _) (sym [[]Env]) (tr (Val _ _) (evals,-aux ez eu) v [ s ]Val) □
        ,+ : evals (z , u) (p [ s ]Env) (env ((w [ s ]Env) , tr (Val _ _) (evals,-aux ez+ eu+) (v [ s ]Val)))
        ,+ = evals, ez+ eu+
evalsπ₁ {X = X} {Y} {Z} {z} {p} {w} {v} ez [ s ]evals = evalsπ₁ (ez [ s ]evals)
isPropEvals x y i [ s ]evals = isPropEvals (x [ s ]evals) (y [ s ]evals) i

_[_]apply {X = X} (lam {A = A} {B} {C} {u} {p} {v} {w} eu) s = lam+'
  where t : (subst (Val _ _) Pi[] (lam u (p [ s ]Env)))
            ⟦ Val _ _ ⟧
            (subst (Val _ _) Pi[] (subst (Val _ _) Pi[] (lam u p) [ s ]Val))
        t = subst (Val _ _) Pi[] (lam u (p [ s ]Env))
            ⟮ ‼ sym (subst-fill (Val _ _) Pi[] (lam u (p [ s ]Env))) ⟯
            lam u (p [ s ]Env)
            ⟮ ‼ trfill (Val _ _) [[]Env] (lam u (p [ s ]Env)) ⟯
            tr (Val _ _) [[]Env] (lam u (p [ s ]Env))
            ⟮ ‼ dcong (_[ s ]Val) (subst-fill (Val _ _) Pi[] (lam u p)) ⟯
            (subst (Val _ _) Pi[] (lam u p) [ s ]Val)
            ⟮ ‼ subst-fill (Val _ _) Pi[] (subst (Val _ _) Pi[] (lam u p) [ s ]Val) ⟯
            (subst (Val _ _) Pi[] (subst (Val _ _) Pi[] (lam u p) [ s ]Val)) □
        P : A [ ⌜ p [ s ]Env ⌝Env ]T ≡ (A [ ⌜ p ⌝Env ]T) [ ⌜ s ⌝Wk ]T
        P = [[]Env]
        S : (A [ ⌜ p [ s ]Env ⌝Env ]T) ≡ ((A [ ⌜ p ⌝Env ]T) [ ⌜ s ⌝Wk ]T)
        S = A [ ⌜ p [ s ]Env ⌝Env ]T
             ≡⟨ cong (A [_]T) ⌜[]Env⌝ ⟩
             A [ ⌜ p ⌝Env ∘t ⌜ s ⌝Wk ]T
             ≡⟨ [∘]T ⟩
             (A [ ⌜ p ⌝Env ]T) [ ⌜ s ⌝Wk ]T ∎
        Q : B [ ⌜ p [ s ]Env ⌝Env ↑ A ]T
            ⟦ Ty _ ⟧
            (B [ ⌜ p ⌝Env ↑ A ]T [ ⌜ s ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T)
        Q = B [ ⌜ p [ s ]Env ⌝Env ↑ A ]T
            ⟮ ‼ dcong (λ x → B [ x ↑ A ]T) ⌜[]Env⌝ ⟯
            B [ (⌜ p ⌝Env ∘t ⌜ s ⌝Wk) ↑ A ]T
            ⟮ hcong (B [_]T) (hsym ↑∘↑) ⟯
            B [ (⌜ p ⌝Env ↑ A) ∘t (⌜ s ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T)) ]T
            ⟮ ‼ [∘]T ⟯
            (B [ ⌜ p ⌝Env ↑ A ]T) [ ⌜ s ⌝Wk ↑ (A [ ⌜ p ⌝Env ]T) ]T □
        lam+ : apply (subst (Val _ _) Pi[] (lam u (p [ s ]Env))) (tr (Val _ _) (sym [[]Env]) (v [ s ]Val)) (w [ s ]Val)
        lam+ = lam (eu [ s ]eval)
        lam+' : apply (subst (Val _ _) Pi[] (subst (Val _ _) Pi[] (lam u p) [ s ]Val)) (v [ s ]Val) (w [ s ]Val)
        lam+' = transport (λ i → apply (hcollapse t (λ i → Pi (P i) (hcollapse Q (cong (X Con.,_) S) i)) i)
                                        (trfill (Val _ _) (sym [[]Env]) (v [ s ]Val) (~ i))
                                        (w [ s ]Val)) lam+
        
neu {A = A} {B} {sv} {v} [ s ]apply = a+'
  where sv+ : Sus _ _ (Pi A B [ ⌜ s ⌝Wk ]T)
        sv+ = sv [ s ]Sus
        sv+' : Sus _ _ (Pi (A [ ⌜ s ⌝Wk ]T) (B [ ⌜ s ⌝Wk ↑ A ]T))
        sv+' = subst (Sus _ _) Pi[] sv+
        n+ = Val.neu sv+'
        n+' = subst (Val _ _) Pi[] (neu sv+)
        n~ : n+ ⟦ Val _ _ ⟧ n+'
        n~ = neu (subst (Sus _ _) Pi[] sv+)
             ⟮ ‼ dcong Val.neu (sym (subst-filler (Sus _ _) Pi[] sv+)) ⟯
             neu sv+
             ⟮ ‼ subst-filler (Val _ _) Pi[] (neu sv+) ⟯
             subst (Val _ _) Pi[] (neu sv+) □
        m+ = neu (app sv+' (v [ s ]Val))
        m+' = neu (tr (Sus _ _) ([<>][] {v = v}) (app sv+' (v [ s ]Val)))
        m~ : m+ ⟦ Val _ _ ⟧ m+'
        m~ = neu (app sv+' (v [ s ]Val))
             ⟮ ‼ dcong Val.neu (trfill (Sus _ _) ([<>][] {v = v}) (app sv+' (v [ s ]Val))) ⟯
             neu (tr (Sus _ _) ([<>][] {v = v}) (app sv+' (v [ s ]Val))) □
        a+ : apply n+ (v [ s ]Val) m+
        a+ = apply.neu {sv = sv+'} {v = v [ s ]Val}
        a+' : apply n+' (v [ s ]Val) m+'
        a+' = transport (λ i → apply (hmerge n~ i) (v [ s ]Val) (hcollapse m~ ([<>][] {v = v}) i)) a+
isPropApply x y i [ s ]apply = isPropApply (x [ s ]apply) (y [ s ]apply) i

_[_]quot : {X Y : Con} {A : Ty n Y} {v : Val n Y A} {w : Nf n Y A}
        → quot v w → (s : Wk X Y) → quot (v [ s ]Val) (w [ s ]Nf)
_[_]quots : {X Y : Con} {A : Ty n Y} {v : Sus n Y A} {w : Nu n Y A}
        → quots v w → (s : Wk X Y) → quots (v [ s ]Sus) (w [ s ]Nu)

_[_]quot {X = X} (quotU {X = Y} {v = v} {w = w} x) s = qx'
  where v+ : Sus _ X (U _ [ ⌜ s ⌝Wk ]T)
        v+ = v [ s ]Sus
        v+' = subst (Sus _ X) U[] v+
        w+ : Nu _ X (U _ [ ⌜ s ⌝Wk ]T)
        w+ = w [ s ]Nu
        w+' = subst (Nu _ X) U[] w+
        x+ : quots v+ w+
        x+ = x [ s ]quots
        x+' : quots v+' w+'
        x+' = transport (λ i → quots (subst-filler (Sus _ X) U[] v+ i)
                                      (subst-filler (Nu _ X) U[] w+ i)) x+
        qx : quot (neu v+') (neuU w+')
        qx = quotU x+'
        qx' : quot (neu v+) (subst (Nf _ X) (sym U[]) (neuU w+'))
        qx' = transport (λ i → quot (neu (subst-filler (Sus _ X) U[] v+ (~ i)))
                                     (subst-filler (Nf _ X) (sym U[]) (neuU w+') i)) qx
_[_]quot {X = X} (quotEl {X = Y} {u = u} {v = v} {w = w} x) s = qx'
  where v+ : Sus _ X (El u [ ⌜ s ⌝Wk ]T)
        v+ = v [ s ]Sus
        v+' = subst (Sus _ X) El[] v+
        w+ : Nu _ X (El u [ ⌜ s ⌝Wk ]T)
        w+ = w [ s ]Nu
        w+' = subst (Nu _ X) El[] w+
        x+ : quots v+ w+
        x+ = x [ s ]quots
        x+' : quots v+' w+'
        x+' = transport (λ i → quots (subst-filler (Sus _ X) El[] v+ i)
                                      (subst-filler (Nu _ X) El[] w+ i)) x+
        qx : quot (neu v+') (neuEl w+')
        qx = quotEl x+'
        qx' : quot (neu v+) (subst (Nf _ X) (sym El[]) (neuEl w+'))
        qx' = transport (λ i → quot (neu (subst-filler (Sus _ X) El[] v+ (~ i)))
                                     (subst-filler (Nf _ X) (sym El[]) (neuEl w+') i)) qx
{--_[_]quot {X = X} (quotL {X = Y} {A = A} {v = v} {w = w} x) s = qx'
  where v+ : Sus _ X (L A [ ⌜ s ⌝Wk ]T)
        v+ = v [ s ]Sus
        v+' = subst (Sus _ X) L[] v+
        w+ : Nu _ X (L A [ ⌜ s ⌝Wk ]T)
        w+ = w [ s ]Nu
        w+' = subst (Nu _ X) L[] w+
        x+ : quots v+ w+
        x+ = x [ s ]quots
        x+' : quots v+' w+'
        x+' = transport (λ i → quots (subst-filler (Sus _ X) L[] v+ i)
                                      (subst-filler (Nu _ X) L[] w+ i)) x+
        qx : quot (neu v+') (neuL w+')
        qx = quotL x+'
        qx' : quot (neu v+) (subst (Nf _ X) (sym L[]) (neuL w+'))
        qx' = transport (λ i → quot (neu (subst-filler (Sus _ X) L[] v+ (~ i)))
                                     (subst-filler (Nf _ X) (sym L[]) (neuL w+') i)) qx--}
_[_]quot {X = X} (quotPi {X = Y} {A} {B} {f} {v} {w} af qv) s = qf+'
  where f+ : Val _ X (Pi A B [ ⌜ s ⌝Wk ]T)
        f+ = f [ s ]Val
        f+' : Val _ X (Pi (A [ ⌜ s ⌝Wk ]T) (B [ ⌜ s ⌝Wk ↑ A ]T))
        f+' = subst (Val _ X) Pi[] f+
        f+'wk = subst (Val _ (X , (A [ ⌜ s ⌝Wk ]T))) Pi[] (f+' [ weakener _ idwk ]Val)
        fwk = subst (Val _ (Y , A)) Pi[] (f [ weakener _ idwk ]Val)
        fwk+ = subst (Val _ (X , A [ ⌜ s ⌝Wk ]T)) Pi[] (fwk [ s ↑Wk A ]Val)
        R' : Pi A B [ ⌜ s ⌝Wk ]T [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T
             ≡
             Pi A B [ ⌜ weakener A idwk ⌝Wk ]T [ ⌜ s ↑Wk A ⌝Wk ]T
        R' = Pi A B [ ⌜ s ⌝Wk ]T [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T
             ≡⟨ sym [∘]T ⟩
             (Pi A B [ ⌜ s ⌝Wk ∘t ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T)
             ≡⟨ cong (λ x → Pi A B [ ⌜ s ⌝Wk ∘t x ]T) ⌜weakener⌝ ⟩
             (Pi A B [ ⌜ s ⌝Wk ∘t (⌜ idwk ⌝Wk ∘t π₁ idt) ]T)
             ≡⟨ cong (λ x → Pi A B [ ⌜ s ⌝Wk ∘t (x ∘t π₁ idt) ]T) ⌜idwk⌝ ⟩
             (Pi A B [ ⌜ s ⌝Wk ∘t (idt ∘t π₁ idt) ]T)
             ≡⟨ cong (λ x → Pi A B [ ⌜ s ⌝Wk ∘t x ]T) id∘ ⟩
             (Pi A B [ ⌜ s ⌝Wk ∘t π₁ idt ]T)
             ≡⟨ cong (Pi A B [_]T) (sym π₁β) ⟩
             (Pi A B [ π₁ (⌜ s ⌝Wk ↑ A) ]T)
             ≡⟨ cong (Pi A B [_]T) (sym id∘) ⟩
             (Pi A B [ idt ∘t π₁ (⌜ s ⌝Wk ↑ A) ]T)
             ≡⟨ cong₂ (λ x y → Pi A B [ x ∘t π₁ y ]T) (sym ⌜idwk⌝) (sym id∘) ⟩
             (Pi A B [ ⌜ idwk ⌝Wk ∘t π₁ (idt ∘t (⌜ s ⌝Wk ↑ A)) ]T)
             ≡⟨ cong (λ x → Pi A B [ ⌜ idwk ⌝Wk ∘t x ]T) π₁∘ ⟩
             (Pi A B [ ⌜ idwk ⌝Wk ∘t (π₁ idt ∘t (⌜ s ⌝Wk ↑ A)) ]T)
             ≡⟨ cong (Pi A B [_]T) (sym ∘∘) ⟩
             Pi A B [ (⌜ idwk ⌝Wk ∘t π₁ idt) ∘t (⌜ s ⌝Wk ↑ A) ]T
             ≡⟨ cong₂ (λ x y → Pi A B [ x ∘t y ]T) (sym ⌜weakener⌝) (sym ⌜↑Wk⌝) ⟩
             (Pi A B [ ⌜ weakener A idwk ⌝Wk ∘t ⌜ s ↑Wk A ⌝Wk ]T)
             ≡⟨ [∘]T ⟩
             Pi A B [ ⌜ weakener A idwk ⌝Wk ]T [ ⌜ s ↑Wk A ⌝Wk ]T ∎
        Q' : ⌜ f [ s ]Val [ weakener (A [ ⌜ s ⌝Wk ]T) idwk ]Val ⌝Val
             ⟦ Tm _ _ ⟧
             ⌜ subst (Val _ _) (sym R') (f [ weakener A idwk ]Val [ s ↑Wk A ]Val) ⌝Val
        Q' = ⌜ f [ s ]Val [ weakener (A [ ⌜ s ⌝Wk ]T) idwk ]Val ⌝Val
             ⟮ ‼ ⌜[]Val⌝ {v = f [ s ]Val} ⟯
             (⌜ f [ s ]Val ⌝Val [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ])
             ⟮ ‼ cong (_[ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]) (⌜[]Val⌝ {v = f}) ⟯
             (⌜ f ⌝Val [ ⌜ s ⌝Wk ] [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ])
             ⟮ hsym [∘] ⟯
             (⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ])
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t x ]) ⌜weakener⌝  ⟯
             (⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t (⌜ idwk ⌝Wk ∘t π₁ idt) ])
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t (x ∘t π₁ idt) ]) ⌜idwk⌝ ⟯
             (⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t (idt ∘t π₁ idt) ])
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t x ]) id∘ ⟯
             ((⌜ f ⌝Val [ ⌜ s ⌝Wk ∘t π₁ idt ]))
             ⟮ ‼ cong (⌜ f ⌝Val [_]) (sym ⌜weakener⌝) ⟯
             (⌜ f ⌝Val [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk ])
             ⟮ ‼ cong (⌜ f ⌝Val [_]) (sym π₁β) ⟯
             (⌜ f ⌝Val [ π₁ (⌜ s ↑Wk A ⌝Wk) ])
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ π₁ x ]) (sym id∘) ⟯
             (⌜ f ⌝Val [ π₁ (idt ∘t ⌜ s ↑Wk A ⌝Wk) ])
             ⟮ ‼ cong (⌜ f ⌝Val [_]) π₁∘ ⟯
             (⌜ f ⌝Val [ π₁ idt ∘t ⌜ s ↑Wk A ⌝Wk ])
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ x ∘t ⌜ s ↑Wk A ⌝Wk ]) (sym id∘) ⟯
             ((⌜ f ⌝Val [ (idt ∘t π₁ idt) ∘t ⌜ s ↑Wk A ⌝Wk ]))
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ (x ∘t π₁ idt) ∘t ⌜ s ↑Wk A ⌝Wk ]) (sym ⌜idwk⌝) ⟯
             ((⌜ f ⌝Val [ (⌜ idwk ⌝Wk ∘t π₁ idt) ∘t ⌜ s ↑Wk A ⌝Wk ]))
             ⟮ ‼ cong (λ x → ⌜ f ⌝Val [ x ∘t ⌜ s ↑Wk A ⌝Wk ]) (sym ⌜weakener⌝) ⟯
             (⌜ f ⌝Val [ ⌜ weakener A idwk ⌝Wk ∘t ⌜ s ↑Wk A ⌝Wk ])
             ⟮ [∘] ⟯ 
             (⌜ f ⌝Val [ ⌜ weakener A idwk ⌝Wk ] [ ⌜ s ↑Wk A ⌝Wk ])
             ⟮ ‼ cong (_[ ⌜ s ↑Wk A ⌝Wk ]) (sym (⌜[]Val⌝ {v = f})) ⟯ 
             (⌜ f [ weakener A idwk ]Val ⌝Val [ ⌜ s ↑Wk A ⌝Wk ])
             ⟮ ‼ sym (⌜[]Val⌝ {v = f [ weakener A idwk ]Val}) ⟯ 
             ⌜ (f [ weakener A idwk ]Val) [ s ↑Wk A ]Val ⌝Val
             ⟮ ‼ dcong ⌜_⌝Val (subst-filler (Val _ _) (sym R') (f [ weakener A idwk ]Val [ s ↑Wk A ]Val)) ⟯
             ⌜ subst (Val _ _) (sym R') (f [ weakener A idwk ]Val [ s ↑Wk A ]Val) ⌝Val □
        p : f+'wk ⟦ Val _ _ ⟧ fwk+
        p = subst (Val _ _) Pi[] (f+' [ weakener _ idwk ]Val)
            ⟮ ‼ sym (subst-filler (Val _ _) Pi[] (f+' [ weakener _ idwk ]Val)) ⟯
            (subst (Val _ _) Pi[] f+) [ weakener _ idwk ]Val
            ⟮ ‼ dcong (_[ weakener (A [ ⌜ s ⌝Wk ]T) idwk ]Val) (sym (subst-filler (Val _ _) Pi[] f+)) ⟯
            ⟨ Val _ _ ((Pi A B [ ⌜ s ⌝Wk ]T) [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T) ⟩
            f [ s ]Val [ weakener (A [ ⌜ s ⌝Wk ]T) idwk ]Val
            ⟮ ‼ veq (hmerge Q') ⟯
            subst (Val _ _) (sym R') (f [ weakener A idwk ]Val [ s ↑Wk A ]Val)
            ⟮ ‼ sym (subst-filler (Val _ _) (sym R') (f [ weakener A idwk ]Val [ s ↑Wk A ]Val)) ⟯
            ⟨ Val _ _ ((Pi A B [ ⌜ weakener A idwk ⌝Wk ]T) [ ⌜ s ↑Wk A ⌝Wk ]T) ⟩
            (f [ weakener A idwk ]Val) [ s ↑Wk A ]Val
            ⟮ ‼ dcong (_[ s ↑Wk A ]Val) (subst-filler (Val _ _) Pi[] (f [ weakener _ idwk ]Val)) ⟯
            (fwk [ s ↑Wk A ]Val)
            ⟮ ‼ subst-filler (Val _ _) Pi[] (fwk [ s ↑Wk A ]Val) ⟯
            subst (Val _ _) Pi[] (fwk [ s ↑Wk A ]Val) □
        Zero+ = tr (Val _ _) idwk-lemma (neu (var (Zero))) [ s ↑Wk A ]Val
        Zero+' = tr (Val _ _) idwk-lemma (neu (var (Zero)))
        q : Zero+ ⟦ Val _ _ ⟧ Zero+'
        q = tr (Val _ _) idwk-lemma (neu (var Zero)) [ s ↑Wk A ]Val
            ⟮ ‼ dcong (_[ s ↑Wk A ]Val) (sym (trfill (Val _ _) idwk-lemma (neu (var Zero)))) ⟯
            neu (var (Zero [ s ↑Wk A ]In))
            ⟮ ‼ dcong (λ x → Val.neu (var x)) (sym (trfill (In _ _) weakening-lemma (tr (In _ _) [⌜weakener⌝] Zero))) ⟯
            neu (var (tr (In _ _) [⌜weakener⌝] Zero))
            ⟮ ‼ dcong (λ x → Val.neu (var x)) (sym (trfill (In _ _) [⌜weakener⌝] Zero)) ⟯
            neu (var Zero)
            ⟮ ‼ trfill (Val _ _) idwk-lemma (neu (var Zero)) ⟯
            (tr (Val _ (X , (A [ ⌜ s ⌝Wk ]T))) idwk-lemma (neu (var Zero))) □            
        P : B [ ⌜ s ↑Wk A ⌝Wk ]T ≡ B [ ⌜ s ⌝Wk ↑ A ]T
        P = cong (B [_]T) ⌜↑Wk⌝
        Q : A [ ⌜ weakener _ idwk ⌝Wk ]T [ ⌜ s ↑Wk A ⌝Wk ]T ≡ A [ ⌜ s ⌝Wk ]T [ ⌜ weakener _ idwk ⌝Wk ]T
        Q = A [ ⌜ weakener _ idwk ⌝Wk ]T [ ⌜ s ↑Wk A ⌝Wk ]T
            ≡⟨ sym [∘]T ⟩
            A [ ⌜ weakener _ idwk ⌝Wk ∘t ⌜ s ↑Wk A ⌝Wk ]T
            ≡⟨ cong (λ x → A [ x ∘t ⌜ s ↑Wk A ⌝Wk ]T) (⌜weakener⌝ ∙ cong (_∘t π₁ idt) ⌜idwk⌝ ∙ id∘) ⟩
            (A [ π₁ idt ∘t ⌜ s ↑Wk A ⌝Wk ]T)
            ≡⟨ cong (A [_]T) (sym π₁∘) ⟩
            (A [ π₁ (idt ∘t ⌜ s ↑Wk A ⌝Wk) ]T)
            ≡⟨ cong (λ x → A [ π₁ x ]T) id∘ ⟩
            (A [ π₁ (⌜ s ↑Wk A ⌝Wk) ]T)
            ≡⟨ cong (A [_]T) π₁β ⟩
            (A [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) s ⌝Wk ]T)
            ≡⟨ cong (A [_]T) ⌜weakener⌝ ⟩
            (A [ ⌜ s ⌝Wk ∘t π₁ idt ]T)
            ≡⟨ cong (λ x → A [ ⌜ s ⌝Wk ∘t x ]T) (sym id∘) ⟩
            (A [ ⌜ s ⌝Wk ∘t (idt ∘t π₁ idt) ]T)
            ≡⟨ cong (λ x → A [ ⌜ s ⌝Wk ∘t (x ∘t π₁ idt) ]T) (sym ⌜idwk⌝) ⟩
            (A [ ⌜ s ⌝Wk ∘t (⌜ idwk ⌝Wk ∘t π₁ idt) ]T)
            ≡⟨ cong (λ x → A [ ⌜ s ⌝Wk ∘t x ]T) (sym ⌜weakener⌝) ⟩
            A [ ⌜ s ⌝Wk ∘t ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T
            ≡⟨ [∘]T ⟩
            (A [ ⌜ s ⌝Wk ]T) [ ⌜ weakener (A [ ⌜ s ⌝Wk ]T) idwk ⌝Wk ]T ∎
        R : B [ ⌜ weakener _ idwk ⌝Wk ↑ A ]T [ ⌜ s ↑Wk A ⌝Wk ↑ (A [ ⌜ weakener _ idwk ⌝Wk ]T) ]T
            ⟦ (λ x → Ty _ x) ⟧
            B [ ⌜ s ⌝Wk ↑ A ]T [ ⌜ weakener _ idwk ⌝Wk ↑ (A [ ⌜ s ⌝Wk ]T) ]T
        R = B [ ⌜ weakener _ idwk ⌝Wk ↑ A ]T [ ⌜ s ↑Wk A ⌝Wk ↑ (A [ ⌜ weakener _ idwk ⌝Wk ]T) ]T
            ⟮ ‼ sym [∘]T ⟯
            B [ (⌜ weakener _ idwk ⌝Wk ↑ A) ∘t (⌜ s ↑Wk A ⌝Wk ↑ (A [ ⌜ weakener _ idwk ⌝Wk ]T)) ]T
            ⟮ hcong (B [_]T) ↑∘↑ ⟯
            (B [ (⌜ weakener A idwk ⌝Wk ∘t (⌜ (s ↑Wk A) ⌝Wk)) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ (x ∘t ⌜ s ↑Wk A ⌝Wk) ↑ A ]T) (⌜weakener⌝ ∙ cong (_∘t π₁ idt) ⌜idwk⌝ ∙ id∘) ⟯
            (B [ (π₁ idt ∘t (⌜ (s ↑Wk A) ⌝Wk)) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ x ↑ A ]T) (sym π₁∘) ⟯
            (B [ (π₁ (idt ∘t ⌜ (s ↑Wk A) ⌝Wk)) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ (π₁ x) ↑ A ]T) id∘ ⟯
            (B [ (π₁ (⌜ (s ↑Wk A) ⌝Wk)) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ x ↑ A ]T) π₁β ⟯
            (B [ (⌜ weakener _ s ⌝Wk) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ x ↑ A ]T) ⌜weakener⌝ ⟯
            (B [ (⌜ s ⌝Wk ∘t π₁ idt) ↑ A ]T)
            ⟮ ‼ cong (λ x → B [ (⌜ s ⌝Wk ∘t x) ↑ A ]T) (sym id∘ ∙ cong (_∘t π₁ idt) (sym ⌜idwk⌝) ∙ sym ⌜weakener⌝) ⟯
            (B [ (⌜ s ⌝Wk ∘t ⌜ weakener _ idwk ⌝Wk) ↑ A ]T)
            ⟮ hcong (B [_]T) (hsym ↑∘↑) ⟯
            (B [ (⌜ s ⌝Wk ↑ A) ∘t (⌜ weakener _ idwk ⌝Wk ↑ (A [ ⌜ s ⌝Wk ]T)) ]T)
            ⟮ ‼ [∘]T ⟯
            B [ ⌜ s ⌝Wk ↑ A ]T [ ⌜ weakener _ idwk ⌝Wk ↑ (A [ ⌜ s ⌝Wk ]T) ]T □
        v+ = v [ s ↑Wk A ]Val
        v+' = subst (Val _ _) P v+
        r = subst-filler (Val _ _) P v+
        $f+ : apply fwk+ Zero+ v+
        $f+ = af [ s ↑Wk A ]apply
        $f+' : apply f+'wk Zero+' v+'
        $f+' = transport (λ i → apply (hcollapse (hsym p) (λ i → Pi (Q i) (hcollapse R (λ i → (_ , Q i)) i)) i)
                                       (hcollapse q Q i)
                                       (r i)) $f+
        w+ = w [ s ↑Wk A ]Nf
        w+' = tr (Nf _ _) P w+
        z = trfill (Nf _ _) P w+
        qw+ : quot v+ w+
        qw+ = qv [ s ↑Wk A ]quot
        qw+' : quot v+' w+'
        qw+' = transport (λ i → quot (r i) (z i)) qw+
        qf+ : quot f+' (lam w+')
        qf+ = quotPi $f+' qw+'
        nf+ = (lam w) [ s ]Nf
        t : lam w+' ⟦ Nf _ _ ⟧ nf+
        t = lam (tr (Nf _ _) P w+)
            ⟮ ‼ dcong Nf.lam (sym (trfill (Nf _ _) P w+)) ⟯
            lam (w [ s ↑Wk A ]Nf)
            ⟮ ‼ dcong Nf.lam (trfill (Nf _ _) [⌜↑⌝] (w [ s ↑Wk A ]Nf)) ⟯
            lam (tr (Nf _ _) [⌜↑⌝] (w [ s ↑Wk A ]Nf))
            ⟮ ‼ subst-filler (Nf _ _) (sym Pi[]) (lam (tr (Nf _ _) [⌜↑⌝] (w [ s ↑Wk A ]Nf))) ⟯
            (subst (Nf _ X) (sym Pi[]) (lam (tr (Nf _ (X , (A [ ⌜ s ⌝Wk ]T))) [⌜↑⌝] (w [ s ↑Wk A ]Nf)))) □
        qf+' : quot f+ nf+
        qf+' = transport (λ i → quot (subst-filler (Val _ _) Pi[] f+ (~ i))
                                      (hcollapse t (sym Pi[]) i)) qf+
        
isPropQuot x y i [ s ]quot = isPropQuot (x [ s ]quot) (y [ s ]quot) i

quotsvar [ s ]quots = quotsvar
_[_]quots {n} {X} (quotsapp {n} {Y} {A} {B} {f} {m} {v} {w} qf qv) s = qfv+'
  where -- Value weakenings
        v+ = v [ s ]Val
        w+ = w [ s ]Nf
        -- Function weakenings
        f+ = f [ s ]Sus
        f+' = subst (Sus _ _) Pi[] f+
        m+ = m [ s ]Nu
        m+' = subst (Nu _ _) Pi[] m+
        -- Value quote weakenings
        qv+ : quot v+ w+
        qv+ = qv [ s ]quot
        -- Function quote weakenings
        qf+ : quots f+ m+
        qf+ = qf [ s ]quots
        qf+' : quots f+' m+'
        qf+' = transport (λ i → quots (subst-filler (Sus _ _) Pi[] f+ i)
                                       (subst-filler (Nu _ _) Pi[] m+ i)) qf+
        fv+ = Sus.app f+' v+
        fv+' = tr (Sus _ _) ([<>][] {v = v}) fv+
        mv+ = tr (λ x → Nu n X (B [ ⌜ s ⌝Wk ↑ A ]T [ < x > ]T)) (sym (quot≡ qv+)) (app m+' w+)
        mv+' = tr (λ x → Nu n Y (B [ < x > ]T)) (sym (quot≡ qv)) (app m w) [ s ]Nu
        p : mv+ ⟦ Nu _ _ ⟧ mv+'
        p = mv+
            ⟮ ‼ sym (trfill (λ x → Nu n X (B [ ⌜ s ⌝Wk ↑ A ]T [ < x > ]T)) (sym (quot≡ qv+)) (app m+' w+)) ⟯
            app m+' w+
            ⟮ ‼ trfill (Nu n X) [<>][]Nf (app m+' w+) ⟯
            tr (Nu n X) ([<>][]Nf {w = w}) (Nu.app m+' w+)
            ⟮ ‼ dcong (_[ s ]Nu) (trfill (λ x → Nu n Y (B [ < x > ]T)) (sym (quot≡ qv)) (app m w)) ⟯
            mv+' □
        qfv+ : quots fv+ mv+
        qfv+ = quotsapp qf+' qv+
        qfv+' : quots fv+' mv+'
        qfv+' = transport (λ i → quots (trfill (Sus _ _) ([<>][] {v = v}) fv+ i)
                                        (hcollapse p ([<>][] {v = v}) i)) qfv+
isPropQuots x y i [ s ]quots = isPropQuots (x [ s ]quots) (y [ s ]quots) i
