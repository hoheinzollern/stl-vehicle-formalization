(******************************************************************************)
(* BoundedSTL.v -- shared bounded-STL vocabulary for the Reuse development.    *)
(*                                                                            *)
(* Bounded STL syntax (form), its Boolean semantics (sat), the Donze--Maler  *)
(* reference robustness (rho) and its sign-soundness (rho_sound), the         *)
(* reduction-nesting depth/window measures (dconj, ddisj, maxwin), and the    *)
(* min/max reductions of nonempty real sequences (SeqMinMax) they rest on.    *)
(* Consumed by MetricChains / ReuseTheorem / ReuseInstances / ReuseQLL.       *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* Part 1: min/max reductions of nonempty real sequences, and the lemmas the *)
(* appendix uses about them (membership, bounds, the paper's Lemma           *)
(* "Non-expansiveness of strict reductions" in pointwise form, behaviour     *)
(* under negation, concatenation and constant padding).                      *)
(******************************************************************************)

Section SeqMinMax.
Variable R : realType.
Implicit Types (s u v : seq R) (x y a b e : R).

Fixpoint rmin s : R :=
  match s with
  | [::] => 0
  | [:: x] => x
  | x :: s' => Num.min x (rmin s')
  end.

Fixpoint rmax s : R :=
  match s with
  | [::] => 0
  | [:: x] => x
  | x :: s' => Num.max x (rmax s')
  end.

Lemma rmin_cons x s : s != [::] -> rmin (x :: s) = Num.min x (rmin s).
Proof. by case: s. Qed.

Lemma rmax_cons x s : s != [::] -> rmax (x :: s) = Num.max x (rmax s).
Proof. by case: s. Qed.

Lemma rmin_mem s : s != [::] -> rmin s \in s.
Proof.
elim: s => [//| x s IH _].
case: s IH => [_| y s' IH]; first by rewrite mem_head.
rewrite rmin_cons //; case: (leP x (rmin (y :: s'))) => h.
- by rewrite mem_head.
- by rewrite in_cons IH ?orbT.
Qed.

Lemma rmax_mem s : s != [::] -> rmax s \in s.
Proof.
elim: s => [//| x s IH _].
case: s IH => [_| y s' IH]; first by rewrite mem_head.
rewrite rmax_cons //; case: (leP (rmax (y :: s')) x) => h.
- by rewrite mem_head.
- by rewrite in_cons IH ?orbT.
Qed.

Lemma rmin_le s x : x \in s -> rmin s <= x.
Proof.
elim: s => [//| y s IH].
rewrite in_cons => /orP[/eqP -> | xs].
- case: s IH => [|z s'] IH; first exact: lexx.
  by rewrite rmin_cons // ge_min lexx.
- case: s xs IH => [//|z s'] xs IH.
  by rewrite rmin_cons // ge_min IH ?orbT.
Qed.

Lemma rmax_ge s x : x \in s -> x <= rmax s.
Proof.
elim: s => [//| y s IH].
rewrite in_cons => /orP[/eqP -> | xs].
- case: s IH => [|z s'] IH; first exact: lexx.
  by rewrite rmax_cons // le_max lexx.
- case: s xs IH => [//|z s'] xs IH.
  by rewrite rmax_cons // le_max IH ?orbT.
Qed.

(* Two-argument distance bounds for min/max: the binary heart of the paper's
   Lemma "Non-expansiveness of strict reductions". *)

Lemma le_min_add x y a b e : x <= y + e -> a <= b + e ->
  Num.min x a <= Num.min y b + e.
Proof.
move=> hx ha; case: (leP y b) => h.
- by rewrite ge_min hx.
- by rewrite ge_min ha orbT.
Qed.

Lemma le_max_add x y a b e : x <= y + e -> a <= b + e ->
  Num.max x a <= Num.max y b + e.
Proof.
move=> hx ha; case: (leP y b) => h.
- rewrite ge_max ha andbT.
  by apply: le_trans hx _; rewrite lerD2r.
- rewrite ge_max hx /=.
  by apply: le_trans ha _; rewrite lerD2r; apply: ltW.
Qed.

Lemma dist_min x y a b e :
  `|x - y| <= e -> `|a - b| <= e -> `|Num.min x a - Num.min y b| <= e.
Proof.
rewrite !ler_distl => /andP[h1 h2] /andP[h3 h4].
apply/andP; split.
- by rewrite lerBlDr; apply: le_min_add; rewrite -lerBlDr.
- exact: le_min_add h2 h4.
Qed.

Lemma dist_max x y a b e :
  `|x - y| <= e -> `|a - b| <= e -> `|Num.max x a - Num.max y b| <= e.
Proof.
rewrite !ler_distl => /andP[h1 h2] /andP[h3 h4].
apply/andP; split.
- by rewrite lerBlDr; apply: le_max_add; rewrite -lerBlDr.
- exact: le_max_add h2 h4.
Qed.

(* Lemma "Non-expansiveness of strict reductions", in the pointwise form the
   induction uses: if two windows are pointwise e-close, so are their
   reductions. *)

Lemma rmin_dist u v e :
  size u = size v -> u != [::] ->
  (forall i, (i < size u)%N -> `|nth 0 u i - nth 0 v i| <= e) ->
  `|rmin u - rmin v| <= e.
Proof.
elim: u v => [|x u IH] [|y v] // [sz] _ hp.
case: u sz IH hp => [|x' u'] sz IH hp.
- by case: v sz hp => [_ hp|//]; exact: (hp 0%N isT).
case: v sz hp => [//|y' v'] sz hp.
rewrite (rmin_cons x) // (rmin_cons y) //.
apply: dist_min; first exact: (hp 0%N isT).
apply: IH => //.
by move=> i hi; exact: (hp i.+1 hi).
Qed.

Lemma rmax_dist u v e :
  size u = size v -> u != [::] ->
  (forall i, (i < size u)%N -> `|nth 0 u i - nth 0 v i| <= e) ->
  `|rmax u - rmax v| <= e.
Proof.
elim: u v => [|x u IH] [|y v] // [sz] _ hp.
case: u sz IH hp => [|x' u'] sz IH hp.
- by case: v sz hp => [_ hp|//]; exact: (hp 0%N isT).
case: v sz hp => [//|y' v'] sz hp.
rewrite (rmax_cons x) // (rmax_cons y) //.
apply: dist_max; first exact: (hp 0%N isT).
apply: IH => //.
by move=> i hi; exact: (hp i.+1 hi).
Qed.

(* Reductions and negation: rho^star = sigma * rho relies on these. *)

Lemma map_consE (T1 T2 : Type) (f : T1 -> T2) z l :
  [seq f i | i <- z :: l] = f z :: [seq f i | i <- l].
Proof. by []. Qed.

Lemma rmaxN s : s != [::] -> rmax [seq - x | x <- s] = - rmin s.
Proof.
elim: s => [//| x s IH _].
case: s IH => [//| y s'] IH.
by rewrite map_consE rmax_cons // IH // (rmin_cons x) // oppr_min.
Qed.

Lemma rminN s : s != [::] -> rmin [seq - x | x <- s] = - rmax s.
Proof.
elim: s => [//| x s IH _].
case: s IH => [//| y s'] IH.
by rewrite map_consE rmin_cons // IH // (rmax_cons x) // oppr_max.
Qed.

Lemma map_mul1 (l : seq R) : [seq 1 * x | x <- l] = l.
Proof. by elim: l => [//| x l IH] /=; rewrite mul1r IH. Qed.

Lemma map_mulN1 (l : seq R) : [seq (- 1) * x | x <- l] = [seq - x | x <- l].
Proof. by elim: l => [//| x l IH] /=; rewrite mulN1r IH. Qed.

(* Concatenation and constant padding (used by the STLLoss instantiation). *)

Lemma rmin_cat s1 s2 : s1 != [::] -> s2 != [::] ->
  rmin (s1 ++ s2) = Num.min (rmin s1) (rmin s2).
Proof.
elim: s1 => [//| x s1 IH _ h2].
case: s1 IH => [| y s1'] IH.
- by rewrite cat1s rmin_cons.
- by rewrite cat_cons (rmin_cons x) // IH // minA (rmin_cons x).
Qed.

Lemma rmax_cat s1 s2 : s1 != [::] -> s2 != [::] ->
  rmax (s1 ++ s2) = Num.max (rmax s1) (rmax s2).
Proof.
elim: s1 => [//| x s1 IH _ h2].
case: s1 IH => [| y s1'] IH.
- by rewrite cat1s rmax_cons.
- by rewrite cat_cons (rmax_cons x) // IH // maxA (rmax_cons x).
Qed.

Lemma rmin_nseq n x : rmin (nseq n.+1 x) = x.
Proof.
elim: n => [//| n IH].
have -> : nseq n.+2 x = x :: nseq n.+1 x by [].
by rewrite rmin_cons // IH minxx.
Qed.

Lemma rmax_nseq n x : rmax (nseq n.+1 x) = x.
Proof.
elim: n => [//| n IH].
have -> : nseq n.+2 x = x :: nseq n.+1 x by [].
by rewrite rmax_cons // IH maxxx.
Qed.

End SeqMinMax.

(* Keep the reductions folded under simplification: proofs below match on   *)
(* the shapes [rmin (...)], [rmax (...)] syntactically.                      *)
Arguments rmin : simpl never.
Arguments rmax : simpl never.

(******************************************************************************)
(* Part 2: bounded STL, its Boolean semantics, the Donze--Maler reference     *)
(* robustness, and the reduction depth/window measures.                       *)
(******************************************************************************)

Section BoundedSTL.

Variable R : realType.
Variable V : Type.                       (* the signal's value space *)
Notation signal := (nat -> V).

(* -------------------------------------------------------------------- *)
(* The abstract non-temporal layer.  A leaf carries a boolean semantics  *)
(* and a Donze--Maler robustness; sign-soundness of the latter is the    *)
(* standard property recorded in Definition "robustness".                *)

Variable NT : Type.
Variable nt_sat : NT -> signal -> nat -> Prop.
Variable nt_rho : NT -> signal -> nat -> R.
Hypothesis nt_rho_pos : forall p s t, 0 < nt_rho p s t -> nt_sat p s t.
Hypothesis nt_rho_neg : forall p s t, nt_rho p s t < 0 -> ~ nt_sat p s t.

(* -------------------------------------------------------------------- *)
(* Bounded STL formulae: temporal structure over non-temporal leaves.    *)
(* This is exactly the fragment covered by the paper's induction (base   *)
(* case: any non-temporal formula; inductive cases: neg, G, F, U).       *)

Inductive form : Type :=
  | FAtom of NT
  | FNeg of form
  | FGlobally of nat & nat & form
  | FFinally of nat & nat & form
  | FUntil of nat & nat & form & form.

(* Window of offsets of the bounded interval [a, b].  With truncated     *)
(* subtraction a degenerate b < a behaves like [a, a]; windows are       *)
(* nonempty by construction, so no well-formedness side conditions are   *)
(* needed anywhere.                                                      *)
Definition win (a b : nat) : seq nat := iota a (b - a).+1.
Arguments win : simpl never.

(* Boolean semantics (Section "Signal Temporal Logic"; until is the      *)
(* Maler--Nickovic strong until: psi at the witness j, phi on [t, t+j)). *)
Fixpoint sat (phi : form) (s : signal) (t : nat) : Prop :=
  match phi with
  | FAtom p => nt_sat p s t
  | FNeg psi => ~ sat psi s t
  | FGlobally a b psi => forall i, i \in win a b -> sat psi s (t + i)
  | FFinally a b psi => exists2 i, i \in win a b & sat psi s (t + i)
  | FUntil a b psi chi =>
      exists2 j, j \in win a b &
        sat chi s (t + j) /\ (forall i, (i < j)%N -> sat psi s (t + i))
  end.

(* Donze--Maler quantitative robustness (Definition "robustness").       *)
Fixpoint rho (phi : form) (s : signal) (t : nat) : R :=
  match phi with
  | FAtom p => nt_rho p s t
  | FNeg psi => - rho psi s t
  | FGlobally a b psi => rmin [seq rho psi s (t + i) | i <- win a b]
  | FFinally a b psi => rmax [seq rho psi s (t + i) | i <- win a b]
  | FUntil a b psi chi =>
      rmax [seq rmin (rho chi s (t + j)
                      :: [seq rho psi s (t + i) | i <- iota 0 j])
           | j <- win a b]
  end.

(* One-step equations for rho, used to unfold the semantics in a         *)
(* controlled way (simpl would unfold win/iota/map too far).             *)
Lemma rho_negE psi s t : rho (FNeg psi) s t = - rho psi s t.
Proof. by []. Qed.

Lemma rho_GE a b psi s t :
  rho (FGlobally a b psi) s t = rmin [seq rho psi s (t + i) | i <- win a b].
Proof. by []. Qed.

Lemma rho_FE a b psi s t :
  rho (FFinally a b psi) s t = rmax [seq rho psi s (t + i) | i <- win a b].
Proof. by []. Qed.

Lemma rho_UE a b psi chi s t :
  rho (FUntil a b psi chi) s t
  = rmax [seq rmin (rho chi s (t + j)
                    :: [seq rho psi s (t + i) | i <- iota 0 j])
         | j <- win a b].
Proof. by []. Qed.

(* Sign-soundness of Donze--Maler robustness: rho > 0 implies sat, and   *)
(* rho < 0 implies ~ sat ('positive exactly when the boolean reading is  *)
(* true', up to the boundary rho = 0).                                   *)
Lemma rho_sound phi s t :
  (0 < rho phi s t -> sat phi s t) /\ (rho phi s t < 0 -> ~ sat phi s t).
Proof.
move: t; elim: phi => [p|psi IH|a b psi IH|a b psi IH|a b psi IHp chi IHc] t;
  split => /=.
- exact: nt_rho_pos.
- exact: nt_rho_neg.
- by rewrite oppr_gt0 => /(proj2 (IH t)).
- by rewrite oppr_lt0 => /(proj1 (IH t)) hs hns; exact: hns hs.
- move=> h i hi; apply: (proj1 (IH (t + i)%N)).
  apply: lt_le_trans h _; apply: rmin_le.
  exact: (map_f (fun i => rho psi s (t + i)%N) hi).
- move=> h hall.
  case/mapP: (rmin_mem (s:=[seq rho psi s (t + i)%N | i <- win a b]) isT)
    => i hi heq.
  apply: (proj2 (IH (t + i)%N)) _ (hall i hi).
  by rewrite -heq.
- move=> h.
  case/mapP: (rmax_mem (s:=[seq rho psi s (t + i)%N | i <- win a b]) isT)
    => i hi heq.
  exists i => //; apply: (proj1 (IH (t + i)%N)).
  by rewrite -heq.
- move=> h [i hi hsat].
  apply: (proj2 (IH (t + i)%N)) _ hsat.
  apply: le_lt_trans h; apply: rmax_ge.
  exact: (map_f (fun i => rho psi s (t + i)%N) hi).
- move=> h.
  case/mapP: (rmax_mem
      (s:=[seq rmin (rho chi s (t + j)%N
                     :: [seq rho psi s (t + i)%N | i <- iota 0 j])
          | j <- win a b]) isT) => j hj heq.
  have h0 : 0 < rmin (rho chi s (t + j)%N
                      :: [seq rho psi s (t + i)%N | i <- iota 0 j]).
    by rewrite -heq.
  exists j => //; split.
  + apply: (proj1 (IHc (t + j)%N)).
    exact: lt_le_trans h0 (rmin_le (mem_head _ _)).
  + move=> i hij; apply: (proj1 (IHp (t + i)%N)).
    apply: lt_le_trans h0 _; apply: rmin_le.
    rewrite in_cons; apply/orP; right.
    apply: (map_f (fun i => rho psi s (t + i)%N)).
    by rewrite mem_iota add0n hij andbT.
- move=> h [j hj [hchi hpsi]].
  have hin : rmin (rho chi s (t + j)%N
                   :: [seq rho psi s (t + i)%N | i <- iota 0 j]) < 0.
    apply: le_lt_trans h; apply: rmax_ge.
    exact: (map_f (fun j => rmin (rho chi s (t + j)%N
                     :: [seq rho psi s (t + i)%N | i <- iota 0 j])) hj).
  have := rmin_mem (s:=rho chi s (t + j)%N
                      :: [seq rho psi s (t + i)%N | i <- iota 0 j]) isT.
  rewrite in_cons => /orP[/eqP heq | /mapP[i hi heq]].
  + by apply: (proj2 (IHc (t + j)%N)) _ hchi; rewrite -heq.
  + move: hi; rewrite mem_iota add0n => /andP[_ hij].
    apply: (proj2 (IHp (t + i)%N)) _ (hpsi i hij).
    by rewrite -heq.
Qed.

(* Reduction-nesting depths d_and, d_or.                                 *)
Fixpoint dconj (phi : form) : nat :=
  match phi with
  | FAtom _ => 0
  | FNeg psi => dconj psi
  | FGlobally _ _ psi => (dconj psi).+1
  | FFinally _ _ psi => dconj psi
  | FUntil _ _ psi chi => (maxn (dconj psi) (dconj chi)).+1
  end.

Fixpoint ddisj (phi : form) : nat :=
  match phi with
  | FAtom _ => 0
  | FNeg psi => ddisj psi
  | FGlobally _ _ psi => ddisj psi
  | FFinally _ _ psi => (ddisj psi).+1
  | FUntil _ _ psi chi => (maxn (ddisj psi) (ddisj chi)).+1
  end.

(* Maximum reduction-window length across phi's temporal operators (the  *)
(* appendix's W): b - a + 1 for G/F; for U the worst inner conjunction   *)
(* has length j + 1 with j ranging over the window, so its last offset   *)
(* a + (b - a) dominates both the inner and the outer window.            *)
Fixpoint maxwin (phi : form) : nat :=
  match phi with
  | FAtom _ => 0
  | FNeg psi => maxwin psi
  | FGlobally a b psi => maxn (b - a).+1 (maxwin psi)
  | FFinally a b psi => maxn (b - a).+1 (maxwin psi)
  | FUntil a b psi chi =>
      maxn (a + (b - a)).+1 (maxn (maxwin psi) (maxwin chi))
  end.

End BoundedSTL.
