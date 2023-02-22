{-# OPTIONS --cubical #-}
module Stability where

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
open import EvalSpec

private variable n : ℕ

norm : {X : Con} {A : Ty n X} → Tm n X A → Nf n X A → Set
norm {X = X} {A} u w = Σ[ v ∈ Val _ X A ] Σ (eval u idenv v) (λ _ → quot v w)

complete : {X : Con} {A : Ty n X} → {u : Tm n X A} → {w : Nf n X A} → norm u w → ⌜ w ⌝Nf ≡ u
complete {u = u} {w = w} (v , e , q) = hmerge P
  where P : ⌜ w ⌝Nf ⟦ Tm _ _ ⟧ u
        P = ⌜ w ⌝Nf
            ⟮ ‼ sym (quot≡ q) ⟯
            ⌜ v ⌝Val
            ⟮ eval≡ e ⟯
            u [ ⌜ idenv ⌝Env ]
            ⟮ ‼ cong (_ [_]) idenv≡ ⟯
            u [ idt ]
            ⟮ [id] ⟯
            u □

norm-sound : {X : Con} {A : Ty n X} → {u : Tm n X A} → {w m : Nf n X A} → norm u w → norm u m → w ≡ m
norm-sound {w = w} {m = m} (v , eval , q) (v' , eval' , q') = quot-sound q (subst (λ x → quot x m) (sym s) q')
   where s : v ≡ v'
         s = hmerge (evalSound eval eval')

isPropNorm : {X : Con} {A : Ty n X} {u : Tm n X A} {w : Nf n X A} → isProp (norm u w)
isPropNorm {X = X} {A} {u} {w} (x , ev , qu) (y , ev' , qu') i = hmerge (evalSound ev ev') i
                                                               , isPropPath {B = λ i → eval u idenv (hmerge (evalSound ev ev') i)} isPropEval ev ev' i
                                                               , isPropPath {B = λ i → quot (hmerge (evalSound ev ev') i) w} isPropQuot qu qu' i

stabilityInAux : {X Y : Con} {A : Ty n Y} {x : In n Y A} {s : Wk X Y}
            → eval ⌜ x ⌝In (idenv [ s ]Env) (neu (var (x [ s ]In)))
stabilityInAux {X = X} {_} {_} {Zero {X = Y} {A = A}} {s , x} = evz'
  where Q : ⌜ idenv [ weakener A idwk ]Env ⌝Env ≡ wk
        Q = ⌜ idenv [ weakener A idwk ]Env ⌝Env
            ≡⟨ ⌜[]Env⌝ {p = idenv} {s = weakener A idwk} ⟩
            ⌜ idenv ⌝Env ∘t ⌜ weakener A idwk ⌝Wk
            ≡⟨ cong₂ _∘t_ idenv≡ ⌜weakener⌝ ⟩
            idt ∘t (⌜ idwk ⌝Wk ∘t π₁ idt)
            ≡⟨ id∘ ⟩
            ⌜ idwk ⌝Wk ∘t π₁ idt
            ≡⟨ cong (_∘t π₁ idt) ⌜idwk⌝ ⟩
            idt ∘t π₁ idt
            ≡⟨ id∘ ⟩
            π₁ idt ∎
        P1 = idenv [ weakener A idwk ]Env [ s , x ]Env
        P2 = tr (Val _ _) (sym [[]Env]) (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val)
        N1 = neu (var (tr (In _ _) weakening-lemma x))
        N2 = neu (var (subst (λ x → In _ _ (A [ x ]T)) (sym Q) Zero)) [ s , x ]Val
        P3 = tr (Val (universe A) _) (sym [[]Env]) N2
        P3≡P2 : P3 ⟦ Val _ _ ⟧ P2
        P3≡P2 = tr (Val _ _) (sym [[]Env]) N2
                 ⟮ ‼ sym (trfill (Val _ _) (sym [[]Env]) N2) ⟯
                 neu (var (subst (λ x → In _ _ (A [ x ]T)) (sym Q) Zero)) [ s , x ]Val
                 ⟮ ‼ dcong (λ i → neu (var i) [ s , x ]Val) (sym (subst-filler (λ x → In _ _ (A [ x ]T)) (sym Q) Zero)) ⟯
                 neu (var (tr (In _ _) weakening-lemma x))
                 ⟮ ‼ dcong (λ i → i [ s , x ]Val) (trfill (Val _ _) [⌜id[E]⌝] (neu (var Zero))) ⟯
                 (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val)
                 ⟮ ‼ trfill (Val _ _) (sym [[]Env]) (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val) ⟯
                 P2 □
        N2≡N1 : N2 ⟦ Val _ _ ⟧ N1
        N2≡N1 = N2
                ⟮ ‼ dcong (λ i → neu (var i) [ s , x ]Val) (sym (subst-filler (λ x → In _ _ (A [ x ]T)) (sym Q) Zero)) ⟯
                neu (var (tr (In _ _) weakening-lemma x)) □
        evz : eval (π₂-boxed {A = A} (box idt)) (env (P1 , P3)) N2
        evz = _[_]eval {w = neu (var (subst (λ x → In _ _ (A [ x ]T)) (sym Q) Zero))} (evalπ₂ evalsid) ( s , x )
        evz' : eval vz (env (P1 , P2)) N1
        evz' = transport (λ i → eval vz (env (P1 , hmerge P3≡P2 i)) (hcollapse N2≡N1 (cong (λ i → A [ i ]T [ ⌜ s ⌝Wk , ⌜ x ⌝In ]T) Q) i)) evz
stabilityInAux {X = X} {_} {_} {Suc z} {s , x} = evs'
  where Q1 : ⌜ s ⌝Wk ≡ ⌜ idenv [ s ]Env ⌝Env
        Q1 = ⌜ s ⌝Wk
             ≡⟨ sym id∘ ∙ cong (_∘t ⌜ s ⌝Wk) (sym idenv≡) ⟩
             (⌜ idenv ⌝Env ∘t ⌜ s ⌝Wk)
             ≡⟨ sym ⌜[]Env⌝ ⟩
             ⌜ idenv [ s ]Env ⌝Env ∎
        evalx : eval ⌜ z ⌝In (idenv [ s ]Env) (neu (var (z [ s ]In)))
        evalx = stabilityInAux {x = z} {s = s}
        P0 = (idenv [ s ]Env)
        P1 = idenv [ weakener _ idwk ]Env [ s , x ]Env
        P0≡P1 : P0 ≡ P1
        P0≡P1 = eeq (⌜ P0 ⌝Env
                    ≡⟨ ⌜[]Env⌝ ⟩
                    (⌜ idenv ⌝Env ∘t ⌜ s ⌝Wk)
                    ≡⟨ cong (⌜ idenv ⌝Env ∘t_) (sym π₁β) ⟩
                    (⌜ idenv ⌝Env ∘t π₁ (⌜ s ⌝Wk , ⌜ x ⌝In))
                    ≡⟨ cong (λ i → ⌜ idenv ⌝Env ∘t π₁ i) (sym id∘) ⟩
                    (⌜ idenv ⌝Env ∘t π₁ (idt ∘t (⌜ s ⌝Wk , ⌜ x ⌝In)))
                    ≡⟨ cong (⌜ idenv ⌝Env ∘t_) π₁∘ ⟩
                    (⌜ idenv ⌝Env ∘t (π₁ idt ∘t (⌜ s ⌝Wk , ⌜ x ⌝In)))
                    ≡⟨ sym ∘∘ ⟩
                    ((⌜ idenv ⌝Env ∘t π₁ idt) ∘t (⌜ s ⌝Wk , ⌜ x ⌝In))
                    ≡⟨ cong (λ i → (⌜ idenv ⌝Env ∘t i) ∘t (⌜ s ⌝Wk , ⌜ x ⌝In)) (sym id∘ ∙ cong (_∘t π₁ idt) (sym ⌜idwk⌝) ∙ sym ⌜weakener⌝) ⟩
                    ((⌜ idenv ⌝Env ∘t ⌜ weakener _ idwk ⌝Wk) ∘t (⌜ s ⌝Wk , ⌜ x ⌝In))
                    ≡⟨ cong (_∘t (⌜ s ⌝Wk , ⌜ x ⌝In)) (sym ⌜[]Env⌝) ⟩
                    (⌜ idenv [ weakener _ idwk ]Env ⌝Env ∘t (⌜ s ⌝Wk , ⌜ x ⌝In))
                    ≡⟨ sym ⌜[]Env⌝ ⟩
                    ⌜ (idenv [ weakener _ idwk ]Env) [ s , x ]Env ⌝Env ∎)
        P2 = neu (var (subst (λ i → In _ _ (_ [ i ]T)) Q1 x))
        P3 = tr (Val _ _) (sym [[]Env]) (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val)
        P2≡P3 : P2 ⟦ Val _ _ ⟧ P3
        P2≡P3 = P2
                ⟮ ‼ dcong (λ i → Val.neu (var i)) (sym (subst-filler (λ i → In _ _ (_ [ i ]T)) Q1 x)) ⟯
                neu (var x)
                ⟮ ‼ dcong (λ i → Val.neu (var i)) (trfill (In _ _) weakening-lemma x) ⟯
                neu (var (tr (In _ _) weakening-lemma x))
                ⟮ ‼ dcong (_[ s , x ]Val) (trfill (Val _ _) [⌜id[E]⌝] (neu (var (Zero)))) ⟯
                (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val)
                ⟮ ‼ trfill (Val _ _) (sym [[]Env]) (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)) [ s , x ]Val) ⟯
                P3 □
        N1 = (neu (var (z [ s ]In)))
        N2 = (neu (var (tr (In _ _) (weakening-lemma {x = x}) (z [ s ]In))))
        N1≡N2 : N1 ⟦ Val _ _ ⟧ N2
        N1≡N2 = ‼ dcong (λ i → Val.neu (var i)) (trfill (In _ _) (weakening-lemma {x = x}) (z [ s ]In))
        evs : eval (⌜ z ⌝In [ π₁ idt ]) (env (P0 , P2)) N1
        evs = eval[] (evalsπ₁ evalsid) evalx
        evs' : eval (vs ⌜ z ⌝In) (env (P1 , P3)) N2
        evs' = transport (λ i → eval (vs ⌜ z ⌝In)
                                      (env (P0≡P1 i , hcollapse P2≡P3 (cong (λ i → _ [ ⌜ i ⌝Env ]T) P0≡P1) i))
                                      (hcollapse N1≡N2 weakening-lemma i)) evs

stabilityIn : {X : Con} {A : Ty n X} {x : In n X A}
           → eval ⌜ x ⌝In idenv (neu (var x))
stabilityIn {X = X} {A} {x = x} = transport (λ i → eval ⌜ x ⌝In (T0 i) (hcollapse T1 T2 i)) S0
   where S0 : eval ⌜ x ⌝In (idenv [ idwk ]Env) (neu (var (x [ idwk ]In)))
         S0 = stabilityInAux {x = x} {s = idwk}
         T0 : idenv {X = X} [ idwk ]Env ≡ idenv
         T0 = eeq (⌜[]Env⌝ {p = idenv} {s = idwk}
                     ∙ cong {B = λ _ → Tms _ _} (⌜ idenv ⌝Env ∘t_) ⌜idwk⌝
                     ∙ ∘id)
         T2 : A [ ⌜ idwk ⌝Wk ]T ≡ A
         T2 = cong (A [_]T) ⌜idwk⌝ ∙ [id]T
         T3 : ⌜ subst (Val _ _) T2 (neu (var (x [ idwk ]In))) ⌝Val ⟦ Tm _ _ ⟧ ⌜ neu (var x) ⌝Val
         T3 = ⌜ subst (Val _ _) T2 (neu (var (x [ idwk ]In))) ⌝Val
              ⟮ ‼ dcong ⌜_⌝Val (sym (subst-fill (Val _ _) T2 (neu (var (x [ idwk ]In))))) ⟯
              ⌜ x [ idwk ]In ⌝In
              ⟮ ‼ ⌜[]In⌝ ⟯
              ⌜ x ⌝In [ ⌜ idwk ⌝Wk ]
              ⟮ ‼ dcong (⌜ x ⌝In [_]) ⌜idwk⌝ ⟯
              ⌜ x ⌝In [ idt ]
              ⟮ [id] ⟯
              ⌜ x ⌝In □
         T1 : neu (var (x [ idwk ]In)) ⟦ Val _ _ ⟧ neu (var x)
         T1 = neu (var (x [ idwk ]In))
              ⟮ ‼ subst-fill (Val _ _) T2 (neu (var (x [ idwk ]In))) ⟯
              subst (Val _ _) T2 (neu (var (x [ idwk ]In)))
              ⟮ ‼ veq (hmerge T3) ⟯
              neu (var x) □

stability : {X : Con} {A : Ty n X} {w : Nf n X A} → norm ⌜ w ⌝Nf w
stabilitys : {X : Con} {A : Ty n X} {w : Nu n X A} → Σ[ v ∈ Sus n X A ] Σ (eval ⌜ w ⌝Nu idenv (neu v)) (λ _ → quots v w)

stability {X = X} {.(Pi _ _)} {lam {A = A} {B = B} w} with stability {w = w}
... | v , ew , qv = subst (Val _ _) T1 (Val.lam ⌜ v ⌝Val idenv)
                  , transport (λ i → eval (lam ⌜ w ⌝Nf) idenv (hcollapse T2 T1 i)) S1
                  , quotPi S3 qv
  where T0 : idenv {X = X} [ idwk ]Env ≡ idenv
        T0 = eeq (⌜[]Env⌝ {p = idenv} {s = idwk}
                ∙ cong {B = λ _ → Tms _ _} (⌜ idenv ⌝Env ∘t_) ⌜idwk⌝
                ∙ ∘id)
        T1 : Pi A B [ ⌜ idenv ⌝Env ]T ≡ Pi A B
        T1 = Pi A B [ ⌜ idenv ⌝Env ]T
             ≡⟨ cong (Pi A B [_]T) idenv≡ ⟩
             Pi A B [ idt ]T
             ≡⟨ [id]T ⟩
             Pi A B ∎
        T2 : (lam ⌜ w ⌝Nf idenv) ⟦ Val _ _ ⟧ subst (Val _ _) T1 (lam ⌜ v ⌝Val idenv)
        T2 = lam ⌜ w ⌝Nf idenv
             ⟮ ‼ cong (λ x → Val.lam x idenv) (sym (quot≡ qv)) ⟯
             (lam ⌜ v ⌝Val idenv)
             ⟮ ‼ subst-fill (Val _ _) T1 (lam ⌜ v ⌝Val idenv) ⟯
             subst (Val _ _) T1 (lam ⌜ v ⌝Val idenv) □
        S1 : eval (lam ⌜ w ⌝Nf) idenv (lam ⌜ w ⌝Nf idenv)
        S1 = evallam {u = ⌜ w ⌝Nf} {p = idenv}
        V1 = (lam ⌜ w ⌝Nf (idenv [ weakener A idwk ]Env))
        V2 = (subst (Val _ _) T1 (lam ⌜ v ⌝Val idenv) [ weakener A idwk ]Val)
        V1≡V2 : V1 ⟦ Val _ _ ⟧ V2
        V1≡V2 = (lam ⌜ w ⌝Nf (idenv [ weakener A idwk ]Env))
                ⟮ ‼ cong (λ x → Val.lam x (idenv [ weakener A idwk ]Env)) (sym (quot≡ qv)) ⟯
                (lam ⌜ v ⌝Val (idenv [ weakener A idwk ]Env))
                ⟮ ‼ trfill (Val _ _) [[]Env] (lam ⌜ v ⌝Val (idenv [ weakener A idwk ]Env)) ⟯
                (tr (Val _ _) [[]Env] (lam ⌜ v ⌝Val (idenv [ weakener A idwk ]Env)))
                ⟮ ‼ dcong (_[ weakener A idwk ]Val) (subst-fill (Val _ _) T1 (lam ⌜ v ⌝Val idenv)) ⟯
                V2 □
        V3 = (tr (Val _ _) [⌜id[E]⌝] (neu (var Zero)))
        V4 = (tr (Val _ _) idwk-lemma (neu (var Zero)))
        V3≡V4 : V3 ⟦ Val _ _ ⟧ V4
        V3≡V4 = V3
                ⟮ ‼ sym (trfill (Val _ _) [⌜id[E]⌝] (neu (var Zero))) ⟯
                neu (var Zero)
                ⟮ ‼ trfill (Val _ _) idwk-lemma (neu (var Zero)) ⟯
                V4 □
        T3 : ⌜ idenv [ weakener A idwk ]Env ⌝Env ≡ ⌜ weakener A idwk ⌝Wk
        T3 = ⌜ idenv [ weakener A idwk ]Env ⌝Env
             ≡⟨ ⌜[]Env⌝ ⟩
             ⌜ idenv ⌝Env ∘t ⌜ weakener A idwk ⌝Wk
             ≡⟨ cong (_∘t ⌜ weakener A idwk ⌝Wk) idenv≡ ⟩
             idt ∘t ⌜ weakener A idwk ⌝Wk
             ≡⟨ id∘ ⟩
             ⌜ weakener A idwk ⌝Wk ∎
        S2 : apply (subst (Val _ _) Pi[] V1) V3 v
        S2 = lam ew
        S3 : apply (subst (Val _ _) Pi[] V2) V4 v
        S3 = transport (λ i → apply (subst (Val _ _) Pi[] (hcollapse V1≡V2 (cong (Pi A B [_]T) T3) i))
                                      (hcollapse V3≡V4 (cong (A [_]T) T3) i)
                                      v) S2 
stability {X = X} {.(U _)} {neuU x} with stabilitys {w = x}
... | v , ew , qv = neu v , ew , quotU qv
stability {X = X} {.(El _)} {neuEl x} with stabilitys {w = x}
... | v , ew , qv = neu v , ew , quotEl qv
--stability {X = X} {.(L _)} {neuL x} with stabilitys {w = x}
--... | v , ew , qv = neu v , ew , quotL qv
stability {X = X} {A} {nfeq {x = x} {y = y} xy i} = isPropPath {B = λ i → norm (isSetTm _ _ xy xy i i) (nfeq xy i)} isPropNorm
                                                                (stability {w = x})
                                                                (stability {w = y}) i
stability {n} {X = X} {A} {isSetNf x y x≡y₁ x≡y₂ i j} = S i j
  where Cons : Nf n X A → Set
        Cons w = norm ⌜ w ⌝Nf w
        R : (i j : I) → Nf n X A
        R i j = isSetNf x y x≡y₁ x≡y₂ i j
        S : PathP (λ i → PathP (λ j → Cons (R i j)) (stability {w = x}) (stability {w = y}))
                                                      (λ w → stability {w = x≡y₁ w})
                                                      (λ w → stability {w = x≡y₂ w})
        S i j = isPropPath* {B = λ i j → Cons (R i j)} isPropNorm
                             (λ i → stability {w = x})
                             (λ i → stability {w = y})
                             (λ i → stability {w = x≡y₁ i})
                             (λ i → stability {w = x≡y₂ i})
                             i j

stabilitys {X = X} {w = var x} = var x , stabilityIn , quotsvar
stabilitys {X = X} {w = app {A = A} {B = B} w v} with stabilitys {w = w} | stability {w = v}
... | p , ep , qp | q , eq , qq = pq' , ewv' , qpq'
  where pq : Sus _ _ (B [ < ⌜ q ⌝Val > ]T)
        pq = app p q
        pq' : Sus _ _ (B [ < ⌜ v ⌝Nf > ]T)
        pq' = subst (λ x → Sus _ _ (B [ < x > ]T)) (quot≡ qq) pq
        eq' = transport (λ i → eval (subst-fill (Tm _ _) (sym [id]T) ⌜ v ⌝Nf i) idenv q) eq
        T0 = evals,-aux evalsid eq'
        T1 : B ⟦ Ty _ ⟧ B [ ⌜ idenv ⌝Env ↑ A ]T
        T1 = B
             ⟮ ‼ sym [id]T ⟯
             B [ idt ]T
             ⟮ hcong (B [_]T) (hsym ↑id) ⟯
             B [ idt ↑ A ]T
             ⟮ ‼ dcong (λ x → B [ x ↑ A ]T) (sym idenv≡) ⟯
             B [ ⌜ idenv ⌝Env ↑ A ]T □
        T2 : Pi A B ≡ Pi (A [ ⌜ idenv ⌝Env ]T) (B [ ⌜ idenv ⌝Env ↑ A ]T)
        T2 i = Pi (T0 i) (hcollapse T1 (cong (X ,_) T0) i)
        p' : Sus _ _ (Pi (A [ ⌜ idenv ⌝Env ]T) (B [ ⌜ idenv ⌝Env ↑ A ]T))
        p' = subst (Sus _ _) T2 p
        q' : Val _ _ (A [ ⌜ idenv ⌝Env ]T)
        q' = subst (Val _ _) T0 q
        ewv : eval (⌜ w ⌝Nu $ ⌜ v ⌝Nf) idenv (neu (app p q))
        ewv = eval[] (evals, evalsid eq')
                     (evalapp (transport (λ i → eval ⌜ w ⌝Nu idenv (subst-fill (Val _ _) T2 (neu p) i)) ep)
                              ((transport (λ i → apply (subst-fill (Val _ _) T2 (neu p) i)
                                                       (trfill (Val _ _) T0 q i)
                                                       (neu (app p q)))
                                         (apply.neu {sv = p} {v = q}))))
        ewv' : eval (⌜ w ⌝Nu $ ⌜ v ⌝Nf) idenv (neu (subst (λ x → Sus _ _ (B [ < x > ]T)) (quot≡ qq) (app p q)))
        ewv' = transport (λ i → eval (⌜ w ⌝Nu $ ⌜ v ⌝Nf)
                                      idenv
                                      (neu (subst-fill (λ x → Sus _ _ (B [ < x > ]T)) (quot≡ qq) (app p q) i))) ewv
        qpq : quots pq (tr (λ x → Nu _ _ (B [ < x > ]T)) (sym (quot≡ qq)) (app w v))
        qpq = quotsapp qp qq
        qpq' : quots pq' (app w v)
        qpq' = transport (λ i → quots (subst-fill (λ x → Sus _ _ (B [ < x > ]T)) (quot≡ qq) pq i)
                                       (trfill (λ x → Nu _ _ (B [ < x > ]T)) (sym (quot≡ qq)) (app w v) (~ i))) qpq
