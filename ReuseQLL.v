(******************************************************************************)
(* QLL: the log-sum-exp DL as an instance of the abstract reuse theorem      *)
(*                                                                            *)
(* The paper's QLLLoss reduces windows with log-sum-exp at sharpness p.  In  *)
(* the sigma = + orientation used by the abstract development its            *)
(* conjunction is the smooth minimum                                          *)
(*                                                                            *)
(*   lse_min p x y = - p^-1 * ln (expR (- (p * x)) + expR (- (p * y)))       *)
(*                                                                            *)
(* a genuine commutative monoidal operator (associativity is inherited from  *)
(* + through the exponential), monotone and sub-meet on ALL of R -- no       *)
(* working-range restriction needed (inrange := predT).  Its idempotency     *)
(* defect is exact:                                                           *)
(*                                                                            *)
(*   selfpow (lse_min p) x n = x - p^-1 * ln n.+1%:R                         *)
(*                                                                            *)
(* so the W-window deviation is  p^-1 * ln W%:R  -- precisely the paper's    *)
(* delta = (log W) / p, here *derived* from the defect builder rather than   *)
(* assumed.  The final corollary reproduces the paper's                      *)
(*   B = delta_atom + (d_and + d_or) * (log W) / p.                          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals sequences exp.
Require Import MetricChains BoundedSTL ReuseTheorem ReuseInstances.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* the metric-chain instance keyed on the realType presentation *)
#[non_forgetful_inheritance]
HB.instance Definition _ (R : realType) :=
  isMetricChain.Build R ring_display R
    (@rdist_ge0 R) (@rdistC R) (@rdist_triangle R) (@rdistxx R)
    (@rdist_convexl R) (@rdist_convexr R).

Section QLL.
Variable R : realType.
Variable p : R.
Hypothesis p_gt0 : (0 < p)%R.

Definition lse_min (x y : R) : R :=
  - (p^-1 * ln (expR (- (p * x)) + expR (- (p * y)))).

Definition lse_max (x y : R) : R :=
  p^-1 * ln (expR (p * x) + expR (p * y)).

(* ---------------------------------------------------------------------- *)
(* Basic shape lemmas.  All proofs go through the exponential:             *)
(* expR is monotone (ler_expR), positive (expR_gt0), and ln is monotone    *)
(* on positives (ler_ln), with expRK : ln (expR x) = x and                  *)
(* lnK : x \is Num.pos -> expR (ln x) = x, lnM for products,               *)
(* expRD for sums.                                                          *)

(* PROOF SKETCH (le_l): the goal is equivalent (lerN2, ler_pM2l with        *)
(* p^-1 > 0, ler_ln with positivity of both sides) to                       *)
(*   expR (- (p * x)) <= expR (- (p * x)) + expR (- (p * y))                *)
(* which is lerDl + (expR_gt0 => ltW).  Rewrite x as                        *)
(* - (p^-1 * ln (expR (- (p * x)))) first (expRK, mulKf/mulVKf with         *)
(* p != 0 from p_gt0) so both sides have the same shape.                    *)
Lemma lse_min_le_l x y : (lse_min x y <= x)%R.
Proof.
rewrite /lse_min lerNl.
have px : - x = p^-1 * ln (expR (- (p * x))).
  by rewrite expRK mulrN mulKf ?gt_eqF.
rewrite {1}px.
rewrite ler_pM2l ?invr_gt0 //.
rewrite ler_ln ?posrE ?expR_gt0 ?addr_gt0 ?expR_gt0 //.
by rewrite lerDl ltW ?expR_gt0.
Qed.

Lemma lse_min_le_r x y : (lse_min x y <= y)%R.
Proof.
rewrite /lse_min lerNl.
have py : - y = p^-1 * ln (expR (- (p * y))).
  by rewrite expRK mulrN mulKf ?gt_eqF.
rewrite {1}py.
rewrite ler_pM2l ?invr_gt0 //.
rewrite ler_ln ?posrE ?expR_gt0 ?addr_gt0 ?expR_gt0 //.
by rewrite lerDr ltW ?expR_gt0.
Qed.

Lemma lse_min_submeet x y : (lse_min x y <= Num.min x y)%R.
Proof. by rewrite le_min lse_min_le_l lse_min_le_r. Qed.

(* PROOF SKETCH: x <= x' gives expR (- (p * x')) <= expR (- (p * x))        *)
(* (ler_expR, lerN2, ler_pM2l), hence the sums, hence the ln's (ler_ln,     *)
(* positivity by addr_gt0 + expR_gt0), hence the negated scaled values      *)
(* flip back (lerN2, ler_pM2l).                                             *)
Lemma lse_min_monol y : {homo lse_min^~ y : x x' / (x <= x')%O}.
Proof.
move=> x x' hxx.
rewrite /lse_min lerN2 ler_pM2l ?invr_gt0 //.
rewrite ler_ln ?posrE ?addr_gt0 ?expR_gt0 //.
by rewrite lerD2r ler_expR lerN2 ler_pM2l.
Qed.

Lemma lse_min_monor x : {homo lse_min x : y y' / (y <= y')%O}.
Proof.
move=> y y' hyy.
rewrite /lse_min lerN2 ler_pM2l ?invr_gt0 //.
rewrite ler_ln ?posrE ?addr_gt0 ?expR_gt0 //.
by rewrite lerD2l ler_expR lerN2 ler_pM2l.
Qed.

(* ---------------------------------------------------------------------- *)
(* The idempotency defect, exactly.                                        *)
(* PROOF SKETCH: elim: n => [|n IH] /=; first by rewrite ln1 mulr0 subr0?? *)
(* (n = 0: selfpow x 0 = x and ln 1%:R = ln 1 = 0).  Step: rewrite IH      *)
(* /lse_min; the inner argument:                                           *)
(*   - (p * (x - p^-1 * ln n.+1%:R)) = - (p * x) + ln n.+1%:R              *)
(* (mulrBr, mulrA, mulfV (p != 0), opprB...); then                          *)
(* expR (- (p*x) + ln n.+1%:R) = expR (- (p*x)) * n.+1%:R                  *)
(* (expRD, lnK with n.+1%:R \is Num.pos: ltr0Sn).  Factor the sum:          *)
(* expR (-(p*x)) * (1 + n.+1%:R) = expR (-(p*x)) * n.+2%:R (natrD/natr1?)  *)
(* and ln of the product splits (lnM, expR_gt0, ltr0Sn); ln (expR _)        *)
(* collapses (expRK); redistribute to  x - p^-1 * ln n.+2%:R.               *)
Lemma lse_selfpow x n :
  selfpow lse_min x n = (x - p^-1 * ln n.+1%:R)%R.
Proof.
elim: n => [|n IH].
  by rewrite /= ln1 mulr0 subr0.
rewrite /= IH /lse_min.
have key : - (p * (x - p^-1 * ln n.+1%:R)) = - (p * x) + ln n.+1%:R.
  rewrite mulrBr mulrA divff ?gt_eqF // mul1r opprB.
  by rewrite addrC.
rewrite key expRD lnK ?posrE ?ltr0Sn //.
rewrite -{1}[expR (- (p * x))]mulr1 -mulrDr nat1r.
rewrite lnM ?posrE ?expR_gt0 ?ltr0Sn // expRK.
by rewrite mulrDr opprD mulrN opprK mulrA mulVf ?gt_eqF // mul1r.
Qed.

(* the defect bound: p^-1 * ln W                                            *)
(* PROOF SKETCH: rewrite lse_selfpow cdistE; |x - c - x| = c for c >= 0     *)
(* (opprB/addrC + ger0_norm; ln n.+1%:R >= 0 by ln_ge0 : 1 <= x -> ...);    *)
(* then ler_pM2l (p^-1 > 0) + ler_ln on n.+1%:R <= W%:R (ler_nat, n < W).   *)
Lemma lse_defect (W : nat) x n : (n < W)%N ->
  (cdist (selfpow lse_min x n) x <= p^-1 * ln W%:R)%R.
Proof.
move=> hn.
rewrite lse_selfpow cdistE.
have -> : x - p^-1 * ln n.+1%:R - x = - (p^-1 * ln n.+1%:R).
  by rewrite addrAC subrr add0r.
rewrite normrN ger0_norm; last first.
  apply: mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply: ln_ge0; rewrite ler1n.
rewrite ler_pM2l ?invr_gt0 //.
rewrite ler_ln ?posrE ?ltr0Sn //.
  by rewrite ler_nat.
by rewrite ltr0n (leq_ltn_trans _ hn).
Qed.

(* window bound via the defect builder, on the trivial working range        *)
Lemma lse_window_bound (W : nat) (x : R) (s : seq R) :
  (size s < W)%N ->
  (cdist (opfold lse_min x s) (minS x s) <= p^-1 * ln W%:R)%R.
Proof.
move=> hsz.
apply: (monoid_window_bound (W:=W) (inrange:=predT) lse_min_monol lse_min_monor
          (fun x y _ _ => lse_min_submeet x y)) => //.
- by move=> y n _ hn; apply: lse_defect.
- by rewrite all_predT.
Qed.

(* ---------------------------------------------------------------------- *)
(* Dual side: smooth maximum.                                               *)
(* PROOF SKETCH: either dualize each proof, or reduce to the min side via   *)
(* the conjugation  lse_max x y = - lse_min (- x) (- y)  (mulrN, opprK).    *)

Lemma lse_maxE x y : lse_max x y = (- lse_min (- x) (- y))%R.
Proof. by rewrite /lse_max /lse_min opprK !mulrN !opprK. Qed.

Lemma lse_max_superjoin x y : (Num.max x y <= lse_max x y)%O.
Proof.
rewrite lse_maxE lerNr.
have -> : - Num.max x y = Num.min (- x) (- y).
  by rewrite real_oppr_max ?num_real.
exact: lse_min_submeet.
Qed.

Lemma lse_max_monol y : {homo lse_max^~ y : x x' / (x <= x')%O}.
Proof.
move=> x x' hxx.
rewrite !lse_maxE lerN2.
by apply: lse_min_monol; rewrite lerN2.
Qed.

Lemma lse_max_monor x : {homo lse_max x : y y' / (y <= y')%O}.
Proof.
move=> y y' hyy.
rewrite !lse_maxE lerN2.
by apply: lse_min_monor; rewrite lerN2.
Qed.

Lemma lse_max_selfpow x n :
  selfpow lse_max x n = (x + p^-1 * ln n.+1%:R)%R.
Proof.
have conj : forall m, selfpow lse_max x m = - selfpow lse_min (- x) m.
  elim=> [|m IH] /=; first by rewrite opprK.
  rewrite lse_maxE IH.
  by congr (- lse_min _ _); exact: opprK.
rewrite conj lse_selfpow opprB.
by rewrite opprK addrC.
Qed.

Lemma lse_max_window_bound (W : nat) (x : R) (s : seq R) :
  (size s < W)%N ->
  (cdist (opfold lse_max x s) (maxS x s) <= p^-1 * ln W%:R)%R.
Proof.
move=> hsz.
apply: (monoid_window_bound_max (W:=W) (inrange:=predT) lse_max_monol lse_max_monor
          (fun x y _ _ => lse_max_superjoin x y)) => //.
- move=> y n _ hn.
  rewrite lse_max_selfpow cdistE.
  have -> : y + p^-1 * ln n.+1%:R - y = p^-1 * ln n.+1%:R.
    by rewrite addrAC subrr add0r.
  rewrite ger0_norm; last first.
    apply: mulr_ge0; first by rewrite invr_ge0 ltW.
    by apply: ln_ge0; rewrite ler1n.
  rewrite ler_pM2l ?invr_gt0 //.
  rewrite ler_ln ?posrE ?ltr0Sn //.
    by rewrite ler_nat.
  by rewrite ltr0n (leq_ltn_trans _ hn).
- by rewrite all_predT.
Qed.

(* ---------------------------------------------------------------------- *)
(* The QLL reuse corollary: B = delta_atom + (d_and + d_or) * (ln W) / p,   *)
(* the paper's Section "Instantiations" formula, now derived.               *)

Variable V : Type.
Notation signal := (nat -> V).
Variable NT : Type.
Variable nt_sat : NT -> signal -> nat -> Prop.
Variable nt_rho : NT -> signal -> nat -> R.
Hypothesis nt_rho_pos : forall q s t, (0 < nt_rho q s t)%R -> nt_sat q s t.
Hypothesis nt_rho_neg : forall q s t, (nt_rho q s t < 0)%R -> ~ nt_sat q s t.

Variable nt_evalL : NT -> signal -> nat -> R.
Variable delta_atom : R.
Hypothesis delta_atom_ge0 : (0 <= delta_atom)%R.
Hypothesis nt_evalL_atom : forall q s t,
  (`|nt_evalL q s t - nt_rho q s t| <= delta_atom)%R.

Variable Wmax : nat.
Hypothesis Wmax_gt0 : (0 < Wmax)%N.

Definition qll_conj (w : seq R) : R :=
  if w is x :: s then opfold lse_min x s else 0.
Definition qll_disj (w : seq R) : R :=
  if w is x :: s then opfold lse_max x s else 0.

(* PROOF SKETCH: instantiate reuse_quantitative from ReuseDefect with       *)
(* L := R, ineg := -x (oppK/opp_anti/opp_isom from ReuseInstances),         *)
(* theta := 0, inrange := predT, delta_conj := delta_disj :=                *)
(* p^-1 * ln Wmax%:R (>= 0 by ln_ge0 + invr_ge0 + mulr_ge0: Wmax >= 1),     *)
(* strictness by lse_window_bound / lse_max_window_bound; then collapse     *)
(* delta *+ d1 + delta *+ d2 = delta *+ (d1 + d2) (mulrnDr).                *)
Corollary qll_quantitative (phi : form NT) (s : signal) (t : nat) :
  (maxwin phi <= Wmax)%N ->
  (`| evalL qll_conj qll_disj (fun x : R => - x) nt_evalL phi s t
      - rhoL nt_rho (fun x : R => - x) phi s t |
   <= delta_atom + (p^-1 * ln Wmax%:R) *+ (dconj phi + ddisj phi))%R.
Proof.
move=> hW.
set q := p^-1 * ln Wmax%:R.
have qge0 : (0 <= q)%R.
  apply: mulr_ge0; first by rewrite invr_ge0 ltW.
  by apply: ln_ge0; rewrite ler1n.
have hBdef : Bdef q q delta_atom (dconj phi) (ddisj phi)
           = delta_atom + q *+ (dconj phi + ddisj phi).
  by rewrite /Bdef mulrnDr addrA.
rewrite -cdistE -hBdef.
apply: (reuse_quantitative (nt_rho:=nt_rho) (ineg:=fun x : R => - x) _
  (conjL:=qll_conj) (disjL:=qll_disj) (negL:=fun x : R => - x)
  (inrange:=predT) (Wmax:=Wmax) (delta_conj:=q) (delta_disj:=q)
  (delta_atom:=delta_atom)
  qge0 qge0 _ _ (fun x => erefl) (fun x s _ _ => isT) (fun x s _ _ => isT)
  (fun x _ => isT) (nt_evalL:=nt_evalL) (fun _ _ _ => isT) _ s t hW).
- by move=> a b; rewrite !cdistE -opprD normrN distrC.
- by move=> x0 s0 _ _ hsz; apply: lse_window_bound.
- by move=> x0 s0 _ _ hsz; apply: lse_max_window_bound.
- by move=> p0 s0 t0; rewrite cdistE; apply: nt_evalL_atom.
Qed.

End QLL.
