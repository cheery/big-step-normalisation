{-# OPTIONS --cubical #-}
module Lemmas where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (sym)
open import Cubical.Foundations.GroupoidLaws
open import Agda.Primitive
open import Library
open import Syntax

private variable n : ℕ

abstract
    π₂βH : {X Y : Con} → {A : Ty n Y} → {p : Tms X Y} → {u : Tm n X (A [ p ]T)}
        → π₂ (p , u) ⟦ Tm n X ⟧ u
    π₂βH {n} {X = X} {A = A} {p} {u} = ‼ π₂β
                   ● ‼ sym (subst-fill (λ x → Tm n _ (_ [ x ]T)) (sym π₁β) _) 

    [id] : {X : Con} {A : Ty n X} {u : Tm n X A} → u [ idt ] ⟦ Tm n X ⟧ u
    [id] {n} {X} {A} {u} = (u [ idt ])
                       ⟮ ‼ dcong (λ x → x [ idt ]) (subst-fill (Tm n X) (sym [id]T) u) ⟯
                       (subst (Tm n X) (sym [id]T) u [ idt ])
                       ⟮ ‼ subst-fill (Tm n X) (sym [∘]T) _ ⟯
                       subst (Tm n X) (sym [∘]T) (subst (Tm n X) (sym [id]T) u [ idt ])
                       ⟮ hsym π₂βH ⟯
                       π₂ ((idt ∘t idt) , subst (Tm n X) (sym [∘]T) (subst (Tm n X) (sym [id]T) u [ idt ]))
                       ⟮ ‼ sym (dcong π₂ ,∘) ⟯
                       π₂ ((idt , subst (Tm n X) (sym [id]T) u) ∘t idt)
                       ⟮ ‼ dcong π₂ ∘id ⟯
                       π₂ (idt , subst (Tm n X) (sym [id]T) u)
                       ⟮ π₂βH ⟯
                       subst (Tm n X) (sym [id]T) u
                       ⟮ ‼ sym (subst-fill (Tm n X) (sym [id]T) u) ⟯
                       u □

    π₁∘ : {X Y Z : Con} {A : Ty n Z} {p : Tms Y (Z , A)} {v : Tms X Y}
       → π₁ (p ∘t v) ≡ (π₁ p) ∘t v
    π₁∘ {n} {X} {p = p} {v = v} = π₁ (p ∘t v)
                              ≡⟨ sym (cong (λ p → π₁ (p ∘t v)) πη) ⟩
                              π₁ ((π₁ p , π₂ p) ∘t v)
                              ≡⟨ cong π₁ ,∘ ⟩ 
                              π₁ ((π₁ p ∘t v) , subst (Tm n X) (sym [∘]T) (π₂ p [ v ]))
                              ≡⟨ π₁β ⟩
                              (π₁ p) ∘t v ∎

    π₂∘ : {X Y Z : Con} {A : Ty n Z} {p : Tms Y (Z , A)} {v : Tms X Y}
       → π₂ (p ∘t v) ⟦ Tm n X ⟧ (π₂ p) [ v ]
    π₂∘ {n} {X} {A = A} {p = p} {v = v} = π₂ (p ∘t v)
                                      ⟮ ‼ sym (dcong (λ p → π₂ (p ∘t v)) πη) ⟯
                                      π₂ ((π₁ p , π₂ p) ∘t v)
                                      ⟮ ‼ dcong π₂ ,∘ ⟯
                                      π₂ ((π₁ p ∘t v) , subst (Tm n X) (sym [∘]T) (π₂ p [ v ]))
                                      ⟮ π₂βH ⟯
                                      subst (Tm n X) (sym [∘]T) (π₂ p [ v ])
                                      ⟮ ‼ sym (subst-fill (Tm n X) (sym [∘]T) _) ⟯
                                      ((π₂ p) [ v ]) □

    <>∘ : {X Y : Con} {A : Ty n Y} {p : Tms X Y} {u : Tm n Y A}
       → (< u > ∘t p) ≡ (p , u [ p ])
    <>∘ {n} {X} {Y} {A} {p} {u} = < u > ∘t p
                            ≡⟨ ,∘ ⟩
                            (idt ∘t p) , subst (Tm n X) (sym [∘]T) (subst (Tm n Y) (sym [id]T) u [ p ])
                            ≡⟨ dcong₂ (λ x y → term._,_ {A = A} x y) id∘ (hcollapse q (cong (A [_]T) id∘)) ⟩
                            p , (u [ p ]) ∎
      where q : subst (Tm n X) (sym [∘]T) (subst (Tm n Y) (sym [id]T) u [ p ]) ⟦ Tm n X ⟧ u [ p ]
            q = ⟨ Tm n X (A [ idt ∘t p ]T) ⟩ subst (Tm n X) (sym [∘]T) (subst (Tm n Y) (sym [id]T) u [ p ])
                ⟮ ‼ sym (subst-fill (Tm n X) (sym [∘]T) (subst (Tm n Y) (sym [id]T) u [ p ])) ⟯
                subst (Tm n Y) (sym [id]T) u [ p ]
                ⟮ ‼ sym (dcong (_[ p ]) (subst-fill (Tm n Y) (sym [id]T) u)) ⟯
                ⟨ Tm n X (A [ p ]T) ⟩ u [ p ] □

    [∘] : {X Y Z : Con} {A : Ty n Z} {p : Tms Y Z} {v : Tms X Y} {u : Tm n Z A}
       → u [ p ∘t v ] ⟦ Tm n X ⟧ u [ p ] [ v ]
    [∘] {n} {X} {Y} {Z} {A} {p} {v} {u} = ⟨ Tm n X (A [ p ∘t v ]T) ⟩ (u [ p ∘t v ])
                                      ⟮ ‼ dcong (_[ p ∘t v ]) (subst-fill (Tm n Z) (sym [id]T) u) ⟯
                                      subst (Tm n Z) (sym [id]T) u [ p ∘t v ]
                                      ⟮ ‼ subst-fill (Tm n X) (sym [∘]T) _ ⟯
                                      subst (Tm n X) (sym [∘]T) (subst (Tm n Z) (sym [id]T) u [ p ∘t v ])
                                      ⟮ hsym π₂βH ⟯
                                      π₂ ((idt ∘t (p ∘t v)) , subst (Tm n X) (sym [∘]T) (subst (Tm n Z) (sym [id]T) u [ p ∘t v ]))
                                      ⟮ ‼ sym (dcong π₂ ,∘) ⟯
                                      π₂ ((idt , subst (Tm n Z) (sym [id]T) u) ∘t (p ∘t v))
                                      ⟮ ‼ sym (dcong π₂ ∘∘) ⟯
                                      π₂ (((idt , subst (Tm n Z) (sym [id]T) u) ∘t p) ∘t v)
                                      ⟮ π₂∘ ⟯
                                      (π₂ ((idt , subst (Tm n Z) (sym [id]T) u) ∘t p) [ v ])
                                      ⟮ hcong (_[ v ]) π₂∘ ⟯
                                      ((π₂ (idt , subst (Tm n Z) (sym [id]T) u) [ p ]) [ v ])
                                      ⟮ hcong (λ x → x [ p ] [ v ]) π₂βH ⟯
                                      ((subst (Tm n Z) (sym [id]T) u [ p ]) [ v ])
                                      ⟮ ‼ sym (dcong (λ x → x [ p ] [ v ]) (subst-fill (Tm n Z) (sym [id]T) u)) ⟯
                                      ⟨ Tm n X ((A [ p ]T) [ v ]T) ⟩ u [ p ] [ v ] □

    wk, : {X Y : Con} {A : Ty n Y} {p : Tms X Y} {u : Tm n X (A [ p ]T)}
        → π₁ idt ∘t (p , u) ≡ p
    wk, {p = p} {u = u} = π₁ idt ∘t (p , u)
                        ≡⟨ sym π₁∘ ⟩
                        π₁ (idt ∘t (p , u))
                        ≡⟨ cong π₁ id∘ ⟩
                        π₁ (p , u)
                        ≡⟨ π₁β ⟩
                        p ∎

    ↑id : {X : Con} {A : Ty n X} → idt ↑ A ⟦ (λ Y → Tms Y (X , A)) ⟧ idt
    ↑id {n} {X} {A} = ((idt ∘t π₁ idt) , subst (Tm n _) (sym [∘]T) (π₂ idt))
                  ⟮ ‼ (λ i → id∘ {p = π₁ idt} i , hcollapse q (λ k → (P k , (A [ id∘ {p = π₁ idt} k ]T))) i) ⟯
                  (π₁ idt term., π₂ idt)
                  ⟮ ‼ πη ⟯
                  idt □
      where P : Path Con (X , A [ idt ]T) (X , A)
            P = cong (X Con.,_) ([id]T {n} {X} {A})
            q : subst (Tm n _) (sym ([∘]T {Y = X} {Z = X} {A = A} {p = idt})) (π₂ idt) ⟦ (λ(x : Σ Con (Ty n)) → Tm n (fst x) (snd x)) ⟧ π₂-boxed {Y = X} {A = A} (box idt)
            q = ⟨ Tm n (X , (A [ idt ]T)) (A [ idt ∘t π₁ idt ]T) ⟩
                subst (Tm n (X , (A [ idt ]T))) (sym [∘]T) (π₂ idt)
                ⟮ pathh (λ i → ((X , A [ idt ]T) , ([∘]T {A = A} {p = idt} {v = π₁ idt} i)))
                        (sym (subst-fill (Tm n (X , (A [ idt ]T))) (sym [∘]T) (π₂ idt))) ⟯ 
                π₂-boxed {A = A [ idt ]T} (box idt)
                ⟮ pathh (λ i → ((X , [id]T {A = A} i) , ([id]T {A = A} i [ π₁ idt ]T))) (λ i → π₂-boxed {A = [id]T i} (box idt)) ⟯ 
                ⟨ Tm n (X , A) (A [ π₁ idt ]T) ⟩
                π₂ idt □

    vz[,] : {X Y : Con} {A : Ty n Y} {p : Tms X Y} {u : Tm n X (A [ p ]T)}
         → π₂ idt [ p , u ] ⟦ Tm n X ⟧ u
    vz[,] {n} {X} {Y} {A} {p} {u} = π₂ idt [ p , u ]
                                ⟮ hsym π₂∘ ⟯
                                π₂ (idt ∘t (p , u))
                                ⟮ ‼ dcong π₂ id∘ ⟯
                                π₂ (p , u)
                                ⟮ π₂βH ⟯
                                u □

    ↑∘, : {X Y Z : Con} {A : Ty n Z} {p : Tms Y Z} {v : Tms X Y} {u : Tm n X (A [ p ]T [ v ]T)}
       → (p ↑ A) ∘t (v , u) ≡ ((p ∘t v), subst (Tm n X) (sym [∘]T) u)
    ↑∘, {n} {X} {Y} {Z} {A} {p} {v} {u} = (p ↑ A) ∘t (v , u)
                                    ≡⟨ ,∘ ⟩
                                    ((p ∘t π₁ idt) ∘t (v , u)) , subst (Tm n X) (sym [∘]T)
                                                                       (subst (Tm n (Y , (A [ p ]T)))
                                                                              (sym [∘]T) (π₂ idt) [ v , u ])
                                    ≡⟨ (λ i → (P i , hcollapse Q (λ i → A [ P i ]T) i)) ⟩
                                    (p ∘t v), subst (Tm n X) (sym [∘]T) u ∎
      where P : (p ∘t π₁ idt) ∘t (v , u) ≡ p ∘t v
            P = (p ∘t π₁ idt) ∘t (v , u)
                ≡⟨ ∘∘ ⟩
                p ∘t (π₁ idt ∘t (v , u))
                ≡⟨ cong (p ∘t_) wk, ⟩
                p ∘t v ∎
            Q : subst (Tm n X) (sym [∘]T) (subst (Tm n (Y , (A [ p ]T))) (sym [∘]T) (π₂ idt) [ v , u ])
                ⟦ Tm n X ⟧
                subst (Tm n X) (sym [∘]T) u
            Q = subst (Tm n X) (sym [∘]T) (subst (Tm n (Y , (A [ p ]T))) (sym [∘]T) (π₂ idt) [ v , u ])
                ⟮ ‼ sym (subst-fill (Tm n X) (sym [∘]T) _) ⟯
                subst (Tm n (Y , (A [ p ]T))) (sym [∘]T) (π₂ idt) [ v , u ]
                ⟮ ‼ sym (dcong (_[ v , u ]) (subst-fill (Tm n _) (sym [∘]T) (π₂ idt))) ⟯
                π₂ idt [ v , u ]
                ⟮ vz[,] ⟯
                u
                ⟮ ‼ subst-fill (Tm n X) (sym [∘]T) u ⟯
                subst (Tm n X) (sym [∘]T) u □

    ↑∘↑ : {X Y Z : Con} {A : Ty n Z} {p : Tms Y Z} {v : Tms X Y}
       → (p ↑ A) ∘t (v ↑ (A [ p ]T)) ⟦ (λ x → Tms x (Z , A)) ⟧ (p ∘t v) ↑ A
    ↑∘↑ {n} {X} {Y} {Z} {A} {p} {v} = (p ↑ A) ∘t (v ↑ (A [ p ]T))
                                  ⟮ ‼ ↑∘, ⟯
                                  ((p ∘t (v ∘t π₁ idt)) , subst (Tm n (X , ((A [ p ]T) [ v ]T))) (sym [∘]T)
                                                               (subst (Tm n (X , ((A [ p ]T) [ v ]T))) (sym [∘]T) (π₂ idt)))
                                  ⟮ pathh S (λ i → P' i , hcollapse Q (λ i → S i , dcong (A [_]T) P' i) i) ⟯
                                  (((p ∘t v) ∘t π₁ idt) , subst (Tm n (X , (A [ p ∘t v ]T))) (sym [∘]T) (π₂ idt)) □
      where S : (X Con., ((A [ p ]T) [ v ]T) ≡ (X , (A [ p ∘t v ]T)))
            S = cong (X Con.,_) (sym [∘]T)
            P : p ∘t (v ∘t π₁ {A = (A [ p ]T) [ v ]T} idt)
                ⟦ (λ i → Tms i Z) ⟧
                ((p ∘t v) ∘t π₁ {A = A [ p ∘t v ]T} idt)
            P = p ∘t (v ∘t π₁ {A = (A [ p ]T) [ v ]T} idt)
                ⟮ ‼ sym ∘∘ ⟯
                ⟨ Tms (X , ((A [ p ]T) [ v ]T)) Z ⟩ (p ∘t v) ∘t π₁ idt
                ⟮ pathh (dcong (X Con.,_) (sym [∘]T))
                        (dcong (λ i → (p ∘t v) ∘t π₁ {A = i} idt) (sym [∘]T)) ⟯
                ⟨ Tms (X , (A [ p ∘t v ]T)) Z ⟩ (p ∘t v) ∘t π₁ idt  □
            P' : PathP (λ i → Tms (dcong (X Con.,_) (sym ([∘]T {Y = Y} {Z = Z} {A = A} {p = p} {v = v})) i) Z) (p ∘t (v ∘t π₁ idt)) ((p ∘t v) ∘t π₁ idt)
            P' = hcollapse P (dcong (X Con.,_) (sym [∘]T))
            R : A [ p ∘t (v ∘t π₁ {A = A [ p ]T [ v ]T} idt) ]T ≡ ((A [ p ]T) [ v ∘t π₁ idt ]T)
            R = [∘]T
            W : ((A [ p ]T) [ v ∘t π₁ {A = A [ p ]T [ v ]T} idt ]T) ≡ (((A [ p ]T) [ v ]T) [ π₁ {A = (A [ p ]T) [ v ]T } idt ]T)
            W = [∘]T
            Q : subst (Tm n _) (sym ([∘]T {Y = Y} {Z = Z} {A = A} {p = p} {v = v ∘t π₁ idt})) (subst (Tm n _) (sym [∘]T) (π₂ idt))
                ⟦ (λ (i : Σ Con (Ty n)) → Tm n (fst i) (snd i)) ⟧
                subst (Tm n _) (sym ([∘]T {Y = X} {Z = Z} {A = A} {p = p ∘t v} {v = π₁ idt})) (π₂ idt)
            Q = subst (Tm n (X , ((A [ p ]T) [ v ]T))) (sym [∘]T) (subst (Tm n _) (sym [∘]T) (π₂ idt))
                ⟮ pathh (cong {B = λ _ → Σ Con (Ty n)} (_ ,_) R) (sym (subst-fill (Tm n _) (sym [∘]T) (subst (Tm n _) (sym [∘]T) (π₂ idt)))) ⟯
                subst (Tm n _) (sym [∘]T) (π₂ idt)
                ⟮ pathh (cong {B = λ _ → Σ Con (Ty n)} (_ ,_) W) (sym (subst-fill (Tm n _) (sym [∘]T) (π₂ idt))) ⟯
                 ⟨ Tm n (X , ((A [ p ]T) [ v ]T)) (((A [ p ]T) [ v ]T) [ π₁ idt ]T) ⟩
                 π₂-boxed {A = A [ p ]T [ v ]T} (box idt)
                 ⟮ pathh (cong {B = λ _ → Σ Con (Ty n)} (λ x → (X , x) , x [ π₁ idt ]T) (sym [∘]T))
                         (dcong (λ i → π₂-boxed {A = i} (box idt)) (sym [∘]T)) ⟯
                 ⟨ Tm n (X , (A [ p ∘t v ]T)) ((A [ p ∘t v ]T) [ π₁ idt ]T) ⟩
                 π₂-boxed {A = A [ p ∘t v ]T} (box idt)
                 ⟮ pathh (cong {B = λ _ → Σ Con (Ty n)} (_ ,_) (sym [∘]T))
                         (subst-fill (Tm n _) (sym [∘]T) (π₂ idt)) ⟯
                 subst (Tm n (X , (A [ p ∘t v ]T))) (sym [∘]T) (π₂ idt) □

    ↑∘<> : {X Y : Con} {A : Ty n Y} {p : Tms X Y} {u : Tm n X (A [ p ]T)}
        → ((p ↑ A) ∘t < u >) ≡ (p , u)
    ↑∘<> {n} {X} {Y} {A} {p} {u} = (p ↑ A) ∘t < u >
                               ≡⟨ ↑∘, ⟩
                               (p ∘t idt) , subst (Tm n X) (sym [∘]T) (subst (Tm n X) (sym [id]T) u)
                               ≡⟨ dcong₂ (term._,_) ∘id (hcollapse P (cong (A [_]T) ∘id)) ⟩
                               (p , u) ∎
      where P : subst (Tm n X) (sym [∘]T) (subst (Tm n X) (sym [id]T) u) ⟦ Tm n X ⟧ u
            P = subst (Tm n X) (sym [∘]T) (subst (Tm n X) (sym [id]T) u)
                ⟮ ‼ sym (subst-fill (Tm n X) (sym [∘]T) _) ⟯
                subst (Tm n X) (sym [id]T) u
                ⟮ ‼ sym (subst-fill (Tm n X) (sym [id]T) u) ⟯
                u □

    lam[]'' : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {u : Tm n (Y , A) B} {s : Tms X Y}
           → subst (Tm n X) Pi[] ((lam u) [ s ]) ≡ lam (u [ s ↑ A ])
    lam[]'' {n} {X} {Y} {A} {B} {u} {s} = hmerge P
       where P : subst (Tm n X) Pi[] ((lam u) [ s ]) ⟦ Tm n X ⟧ lam (u [ s ↑ A ])
             P = subst (Tm n X) Pi[] ((lam u) [ s ])
                 ⟮ ‼ sym (subst-fill (Tm n X) Pi[] _) ⟯
                 (lam u) [ s ]
                 ⟮ ‼ lam[] ⟯
                 subst (Tm n X) (sym Pi[]) (lam (u [ (s ∘t π₁ idt) , subst (Tm n (X , (A [ s ]T))) (sym [∘]T) (π₂ idt) ]))
                 ⟮ ‼ sym (subst-fill (Tm n X) (sym Pi[]) _) ⟯
                 lam (u [ s ↑ A ]) □

    []app : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {f : Tm n Y (Pi A B)} {s : Tms X Y}
          → app (subst (Tm n X) Pi[] (f [ s ])) ⟦ Tm n (X , A [ s ]T) ⟧ (app f) [ s ↑ A ]
    []app {n} {X} {Y} {A} {B} {f} {s} = app (subst (Tm n X) Pi[] (f [ s ]))
                                    ⟮ ‼ cong {x = f} (λ x → app (subst (Tm n X) Pi[] (x [ s ]))) (sym η) ⟯
                                    app (subst (Tm n X) Pi[] (lam (app f) [ s ]))
                                    ⟮ ‼ cong app lam[]'' ⟯
                                    app (lam ((app f) [ s ↑ A ]))
                                    ⟮ ‼ β ⟯
                                    app f [ s ↑ A ] □

    app[] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {f : Tm n Y (Pi A B)} {s : Tms X (Y , A)}
          → (app f) [ s ] ⟦ Tm n X ⟧ ((subst (Tm n X) Pi[] (f [ π₁ s ])) $ π₂ s)
    app[] {n} {X} {Y} {A} {B} {f} {s} = (app f) [ s ]
                                    ⟮ ‼ dcong ((app f) [_]) (sym πη) ⟯
                                    (app f [ π₁ s , π₂ s ])
                                    ⟮ ‼ dcong ((app f) [_]) (sym ↑∘<>) ⟯
                                    app f [ (π₁ s ↑ A) ∘t < π₂ s > ]
                                    ⟮ [∘] ⟯
                                    (app f [ π₁ s ↑ A ]) [ < π₂ s > ]
                                    ⟮ hcong (_[ < π₂ s > ]) (hsym []app) ⟯
                                    (subst (Tm n X) Pi[] (f [ π₁ s ]) $ π₂ s) □

    $[] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {f : Tm n Y (Pi A B)} {u : Tm n Y A} {s : Tms X Y}
       → ((f $ u) [ s ]) ⟦ Tm n X ⟧ ((subst (Tm n X) Pi[] (f [ s ])) $ (u [ s ]))
    $[] {n} {X} {Y} {A} {B} {f} {u} {s} = (f $ u) [ s ]
                                      ⟮ hsym [∘] ⟯
                                      app f [ < u > ∘t s ]
                                      ⟮ ‼ dcong (app f [_]) <>∘ ⟯
                                      app f [ s , (u [ s ]) ]
                                      ⟮ ‼ sym (dcong (app f [_]) ↑∘<>) ⟯
                                      app f [ (s ↑ A) ∘t < u [ s ] > ]
                                      ⟮ [∘] ⟯
                                      (app f [ s ↑ A ]) [ < u [ s ] > ]
                                      ⟮ hsym (hcong (_[ < u [ s ] > ]) []app) ⟯
                                      (app (subst (Tm n X) Pi[] (f [ s ])) [ < u [ s ] > ]) □

    clos[] : {X Y : Con} {A : Ty n Y} {B : Ty n (Y , A)} {u : Tm n (Y , A) B} {p : Tms X Y} {v : Tm n X (A [ p ]T)}
          → ((subst (Tm n X) Pi[] ((lam u) [ p ])) $ v) ⟦ Tm n X ⟧ u [ p , v ]
    clos[] {n} {X} {Y} {A} {B} {u} {p} {v} = ((subst (Tm n X) Pi[] ((lam u) [ p ])) $ v)
                                         ⟮ ‼ cong (_$ v) lam[]'' ⟯
                                         (lam (u [ p ↑ A ]) $ v)
                                         ⟮ ‼ cong (_[ < v > ]) β ⟯
                                         (u [ p ↑ A ]) [ < v > ]
                                         ⟮ hsym [∘] ⟯
                                         u [ ((p ∘t π₁ idt) , subst (Tm n (X , (A [ p ]T))) (sym [∘]T) (π₂ idt)) ∘t < v > ]
                                         ⟮ ‼ dcong (u [_]) ↑∘<> ⟯
                                         u [ p , v ] □

    classicη : {X : Con} {A : Ty n X} {B : Ty n (X , A)} {f : Tm n X (Pi A B)}
             → lam (subst (Tm n _) Pi[] (f [ π₁ idt ]) $ π₂ idt) ⟦ Tm n X ⟧ f
    classicη {n} {X} {A} {B} {f} = lam (subst (Tm n _) Pi[] (f [ π₁ idt ]) $ π₂ idt)
                               ⟮ ‼ cong {x = f} (λ x → lam ((subst (Tm n _) Pi[] (x [ π₁ idt ])) $ π₂ idt)) (sym η) ⟯
                               lam (subst (Tm n (X , A)) Pi[] (lam (app f) [ π₁ idt ]) $ π₂ idt)
                               ⟮ hcong lam clos[] ⟯
                               lam (app f [ π₁ idt , π₂ idt ])
                               ⟮ ‼ dcong (λ x → lam (app f [ x ])) πη ⟯
                               lam (app f [ idt ])
                               ⟮ hcong lam [id] ⟯
                               lam (app f)
                               ⟮ ‼ η ⟯
                               f □
