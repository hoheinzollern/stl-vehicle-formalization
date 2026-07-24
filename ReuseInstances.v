(******************************************************************************)
(* Instances of the abstract reuse theorem (ReuseDefect.v)                    *)
(*                                                                            *)
(* 1. real_sep: on real chains the separation premise of the boolean part    *)
(*    is literally the margin condition  theta + B < value.                  *)
(* 2. Godel / STLLoss: reductions are the strict min/max themselves          *)
(*    (delta = 0), involution -x, threshold 0, working range predT.  This    *)
(*    recovers the exact Donze-Maler development of ReuseTheorem.v.          *)
(* 3. Kleene-Zadeh: same exact reductions, involution 1 - x, threshold 1/2,  *)
(*    working range [0, 1].  A *bounded* De Morgan (non-residuated!) fuzzy   *)
(*    logic with all-zero slacks: the counterexample to 'only unbounded      *)
(*    robustness supports an involution'.                                    *)
(* 4. Lukasiewicz: monoidal conjunction max(0, x + y - 1) via the defect     *)
(*    builder; W-window idempotency defect  1 - 1/W  (order-1: the bound is  *)
(*    honest but weak, matching the fuzzy-logic folklore that Lukasiewicz    *)
(*    is not n-contractive).                                                  *)
(* 5. DL2: the conjunction + has unbounded idempotency defect even on the    *)
(*    2-element constant window; no finite delta exists.  The paper's DL2    *)
(*    exclusion, as a theorem.                                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import MetricChains BoundedSTL ReuseTheorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* Part 1: the boolean part on real chains is a margin condition             *)
(******************************************************************************)

Section RealSeparation.
Variable R : realDomainType.
Implicit Types x t c : R.

(* PROOF SKETCH: -> direction: apply to y := x - c; `|x - (x - c)| = c      *)
(* (ger0_norm, addrK-style rearrangement); from t < x - c conclude          *)
(* t + c < x (ltrBrDr / lterBDr family).  <- direction: from |x - y| <= c   *)
(* get x - c <= y (ler_distl), and t + c < x gives t < x - c <= y.          *)
Lemma real_sep x t c : (0 <= c)%R ->
  (forall y : R, (`|x - y| <= c)%R -> (t < y)%R) <-> (t + c < x)%R.
Proof.
move=> c0; split.
- move=> H; rewrite -ltrBrDr; apply: H.
  by rewrite opprB addrCA subrr addr0 ger0_norm.
- move=> H y Hy.
  have hxy : x - c <= y.
    by move: Hy; rewrite ler_distl => /andP[_ h]; rewrite lerBlDr.
  have h2 : t < x - c by rewrite ltrBrDr.
  exact: lt_le_trans h2 hxy.
Qed.

Lemma real_sep_lt x t c : (0 <= c)%R ->
  (forall y : R, (`|x - y| <= c)%R -> (y < t)%R) <-> (x < t - c)%R.
Proof.
move=> c0; split.
- move=> H; rewrite ltrBrDr; apply: (H (x + c)).
  by rewrite opprD addrA subrr add0r normrN ger0_norm.
- move=> H y Hy.
  have hxy : y <= x + c.
    by move: Hy; rewrite ler_distl => /andP[h _]; move: h; rewrite lerBlDr addrC.
  by apply: le_lt_trans hxy _; rewrite -ltrBrDr.
Qed.

End RealSeparation.

(******************************************************************************)
(* Part 2: Godel / STLLoss -- exact reductions, involution -x, threshold 0   *)
(******************************************************************************)

Section Godel.
Variable R : realDomainType.
Variable V : Type.
Notation signal := (nat -> V).
Variable NT : Type.
Variable nt_sat : NT -> signal -> nat -> Prop.
Variable nt_rho : NT -> signal -> nat -> R.
Hypothesis nt_rho_pos : forall p s t, (0 < nt_rho p s t)%R -> nt_sat p s t.
Hypothesis nt_rho_neg : forall p s t, (nt_rho p s t < 0)%R -> ~ nt_sat p s t.

Variable nt_evalL : NT -> signal -> nat -> R.
Variable delta_atom : R.
Hypothesis nt_evalL_atom : forall p s t,
  (`|nt_evalL p s t - nt_rho p s t| <= delta_atom)%R.

Variable Wmax : nat.

(* the DL reductions: the strict ones themselves *)
Definition godel_conj (w : seq R) : R :=
  if w is x :: s then minS x s else 0.
Definition godel_disj (w : seq R) : R :=
  if w is x :: s then maxS x s else 0.

(* involution -x: involutive, antitone, isometric, fixes 0 *)
Lemma oppK : involutive (fun x : R => - x).
Proof. exact: opprK. Qed.
Lemma opp_anti : {homo (fun x : R => - x) : x y /~ (x <= y)%O}.
Proof. by move=> x y hxy; rewrite lerN2. Qed.

(* |(-x) - (-y)| = |y - x| = |x - y| *)
Lemma opp_isom (x y : R) : cdist (- x) (- y) = cdist x y.
Proof. by rewrite !cdistE -opprD -opprB normrN opprB. Qed.

(* PROOF SKETCH: instantiate reuse_quantitative from ReuseDefect with       *)
(* L := R (the generic realDomainType metric-chain instance), ineg := -x,   *)
(* theta := 0, inrange := predT, delta_conj := 0, delta_disj := 0.  The     *)
(* strictness conditions are cdistxx + lexx; range conditions are trivial   *)
(* (predT); use About/Check to get the argument order of the section-       *)
(* closed theorem.                                                           *)
Corollary godel_quantitative (phi : form NT) (s : signal) (t : nat) :
  (maxwin phi <= Wmax)%N ->
  (`|evalL godel_conj godel_disj (fun x : R => - x) nt_evalL phi s t
     - rhoL nt_rho (fun x : R => - x) phi s t| <= delta_atom)%R.
Proof.
move=> hW; rewrite -cdistE.
have key := reuse_quantitative (nt_rho:=nt_rho) (ineg:=fun x : R => - x)
  opp_isom (conjL:=godel_conj) (disjL:=godel_disj)
  (negL:=fun x : R => - x) (inrange:=predT) (Wmax:=Wmax)
  (delta_conj:=0) (delta_disj:=0) (delta_atom:=delta_atom)
  (lexx 0) (lexx 0)
  (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (minS x s0)))
  (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (maxS x s0)))
  (fun x => erefl) (fun _ _ _ _ => is_true_true) (fun _ _ _ _ => is_true_true)
  (fun _ _ => is_true_true) (nt_evalL:=nt_evalL) (fun _ _ _ => is_true_true)
  nt_evalL_atom s t hW.
have E : Bdef 0 0 delta_atom (dconj phi) (ddisj phi) = delta_atom.
  by rewrite /Bdef !mul0rn !addr0.
by rewrite -E.
Qed.

(* Boolean corollary with the familiar margin form, via real_sep.           *)
Corollary godel_boolean_sat (phi : form NT) (s : signal) (t : nat) :
  (0 <= delta_atom)%R ->
  (maxwin phi <= Wmax)%N ->
  (delta_atom < evalL godel_conj godel_disj
                  (fun x : R => - x) nt_evalL phi s t)%R ->
  sat nt_sat phi s t.
Proof.
move=> hd hW hlt.
apply: (@reuse_boolean_sat R _ R V NT nt_sat nt_rho (fun x => - x) 0
  opprK opp_anti opp_isom (oppr0 R) nt_rho_pos nt_rho_neg
  godel_conj godel_disj (fun x => - x) predT Wmax 0 0 delta_atom
  (lexx _) (lexx _)
  (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (minS x s0)))
  (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (maxS x s0)))
  (fun x => erefl) (fun _ _ _ _ => is_true_true) (fun _ _ _ _ => is_true_true)
  (fun _ _ => is_true_true) nt_evalL (fun _ _ _ => is_true_true) nt_evalL_atom
  phi s t hW).
have E : Bdef 0 0 delta_atom (dconj phi) (ddisj phi) = delta_atom.
  by rewrite /Bdef !mul0rn !addr0.
rewrite E => y hy.
move: hy; rewrite cdistE => hy.
have := (proj2 (real_sep _ 0 hd)); rewrite add0r => H.
by apply: (H _ hlt y).
Qed.

End Godel.

(******************************************************************************)
(* Part 3: Kleene-Zadeh -- min/max/1-x on [0,1], threshold 1/2               *)
(******************************************************************************)

Section KleeneZadeh.
Variable R : realFieldType.
Variable V : Type.
Notation signal := (nat -> V).
Variable NT : Type.
Variable nt_sat : NT -> signal -> nat -> Prop.
Variable nt_rho : NT -> signal -> nat -> R.

Definition kz_neg (x : R) : R := 1 - x.
Definition kz_theta : R := 2^-1.
Definition kz_range : pred R := [pred x | (0 <= x <= 1)%R].

(* soundness of the reference layer w.r.t. threshold 1/2 *)
Hypothesis nt_rho_pos : forall p s t,
  (kz_theta < nt_rho p s t)%R -> nt_sat p s t.
Hypothesis nt_rho_neg : forall p s t,
  (nt_rho p s t < kz_theta)%R -> ~ nt_sat p s t.
Hypothesis nt_rho_range : forall p s t, kz_range (nt_rho p s t).

Variable Wmax : nat.

(* PROOF SKETCH: 1 - (1 - x) = x by opprB/addrNK arithmetic.                *)
Lemma kz_negK : involutive kz_neg.
Proof. by move=> x; rewrite /kz_neg opprB addrCA subrr addr0. Qed.

Lemma kz_neg_anti : {homo kz_neg : x y /~ (x <= y)%O}.
Proof. by move=> x y hxy; rewrite /kz_neg lerD2l lerN2. Qed.

(* |(1-x) - (1-y)| = |y - x| = |x - y| *)
Lemma kz_neg_isom (x y : R) : cdist (kz_neg x) (kz_neg y) = cdist x y.
Proof.
rewrite !cdistE /kz_neg.
have -> : 1 - x - (1 - y) = y - x.
  by rewrite opprB -addrA [- x + (y - 1)]addrC addrA [1 + (y - 1)]addrCA subrr addr0.
by rewrite distrC.
Qed.

(* 1 - 1/2 = 1/2 *)
Lemma kz_neg_theta : kz_neg kz_theta = kz_theta.
Proof.
rewrite /kz_neg /kz_theta.
apply/eqP; rewrite subr_eq -mulr2n.
have -> : (2^-1 : R) *+ 2 = 2^-1 * 2%:R by rewrite mulr_natr.
by rewrite mulVf // pnatr_eq0.
Qed.

Lemma kz_neg_range x : kz_range x -> kz_range (kz_neg x).
Proof.
rewrite /kz_range /kz_neg !inE => /andP[h0 h1].
by apply/andP; split; [rewrite subr_ge0 | rewrite gerBl].
Qed.

(* range closure of the exact reductions, via minS_mem/maxS_mem + allP     *)
Lemma kz_conj_range (x : R) (s : seq R) : kz_range x -> all kz_range s ->
  kz_range (godel_conj (x :: s)).
Proof.
move=> hx hs.
have hall : all kz_range (x :: s) by rewrite /= hx hs.
by rewrite /godel_conj; move/allP: hall; apply; exact: minS_mem.
Qed.

Lemma kz_disj_range (x : R) (s : seq R) : kz_range x -> all kz_range s ->
  kz_range (godel_disj (x :: s)).
Proof.
move=> hx hs.
have hall : all kz_range (x :: s) by rewrite /= hx hs.
by rewrite /godel_disj; move/allP: hall; apply; exact: maxS_mem.
Qed.

(* The Kleene-Zadeh reuse corollary: exact fragment (nt_evalL := nt_rho),  *)
(* all deltas 0, so B = 0 and any value distinct from 1/2 decides           *)
(* satisfaction.  This instance is the counterexample recorded in the       *)
(* conversation: a bounded De Morgan logic with exact reductions AND an     *)
(* involutive negation (which is not the residual negation of any           *)
(* continuous t-norm: the algebra is De Morgan, not residuated).            *)
Corollary kleene_zadeh_sound (phi : form NT) (s : signal) (t : nat) :
  (maxwin phi <= Wmax)%N ->
  ((kz_theta < evalL (godel_conj (R:=R)) (godel_disj (R:=R)) kz_neg
                 nt_rho phi s t)%R
   -> sat nt_sat phi s t) /\
  ((evalL (godel_conj (R:=R)) (godel_disj (R:=R)) kz_neg
      nt_rho phi s t < kz_theta)%R
   -> ~ sat nt_sat phi s t).
Proof.
move=> hW; split=> hcmp.
- have H := (@reuse_boolean_sat R _ R V NT nt_sat nt_rho kz_neg kz_theta
    kz_negK kz_neg_anti kz_neg_isom kz_neg_theta nt_rho_pos nt_rho_neg
    (godel_conj (R:=R)) (godel_disj (R:=R)) kz_neg kz_range Wmax 0 0 0
    (lexx _) (lexx _)
    (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (minS x s0)))
    (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (maxS x s0)))
    (fun x => erefl) kz_conj_range kz_disj_range kz_neg_range nt_rho nt_rho_range
    (fun p s0 t0 => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (nt_rho p s0 t0)))
    phi s t hW).
  apply: H => y hy.
  have E : Bdef 0 0 0 (dconj phi) (ddisj phi) = 0 :> R.
    by rewrite /Bdef !mul0rn !addr0.
  by move: hy; rewrite E cdistE normr_le0 subr_eq0 => /eqP <-; exact: hcmp.
- have H := (@reuse_boolean_unsat R _ R V NT nt_sat nt_rho kz_neg kz_theta
    kz_negK kz_neg_anti kz_neg_isom kz_neg_theta nt_rho_pos nt_rho_neg
    (godel_conj (R:=R)) (godel_disj (R:=R)) kz_neg kz_range Wmax 0 0 0
    (lexx _) (lexx _)
    (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (minS x s0)))
    (fun x s0 _ _ _ => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (maxS x s0)))
    (fun x => erefl) kz_conj_range kz_disj_range kz_neg_range nt_rho nt_rho_range
    (fun p s0 t0 => eq_ind_r (fun z => (z <= 0)%R) (lexx 0) (cdistxx (nt_rho p s0 t0)))
    phi s t hW).
  apply: H => y hy.
  have E : Bdef 0 0 0 (dconj phi) (ddisj phi) = 0 :> R.
    by rewrite /Bdef !mul0rn !addr0.
  by move: hy; rewrite E cdistE normr_le0 subr_eq0 => /eqP <-; exact: hcmp.
Qed.

End KleeneZadeh.

(******************************************************************************)
(* Part 4: Lukasiewicz -- monoidal conjunction via the defect builder        *)
(******************************************************************************)

Section Lukasiewicz.
Variable R : realFieldType.

Definition luk_conj (x y : R) : R := Num.max 0 (x + y - 1).
Definition luk_disj (x y : R) : R := Num.min 1 (x + y).
Definition luk_range : pred R := [pred x | (0 <= x <= 1)%R].

Lemma luk_conj_monol y : {homo luk_conj^~ y : x x' / (x <= x')%O}.
Proof.
move=> x x' hxx; rewrite /luk_conj.
rewrite ge_max le_max lexx /= le_max.
by rewrite lerD2r lerD2r hxx orbT.
Qed.

Lemma luk_conj_monor x : {homo luk_conj x : y y' / (y <= y')%O}.
Proof.
move=> y y' hyy; rewrite /luk_conj.
rewrite ge_max le_max lexx /= le_max.
by rewrite lerD2r lerD2l hyy orbT.
Qed.

(* on [0,1]: max 0 (x+y-1) <= min x y since x+y-1 <= x (y <= 1) etc.        *)
Lemma luk_conj_submeet x y : luk_range x -> luk_range y ->
  (luk_conj x y <= Order.min x y)%O.
Proof.
rewrite /luk_range /luk_conj !inE => /andP[hx0 hx1] /andP[hy0 hy1].
rewrite ge_max le_min hx0 hy0 /=.
rewrite le_min; apply/andP; split.
- by rewrite -addrA gerDl subr_le0.
- by rewrite addrAC gerDr subr_le0.
Qed.

Lemma luk_conj_range x y : luk_range x -> luk_range y ->
  luk_range (luk_conj x y).
Proof.
rewrite /luk_range /luk_conj !inE => /andP[hx0 hx1] /andP[hy0 hy1].
apply/andP; split.
- by rewrite le_max lexx.
- rewrite ge_max ler01 /= lerBlDr.
  by apply: lerD; rewrite -?(ler01) // (le_trans hx1) // lerDl.
Qed.

(* closed form of the self-power: n+1 copies of x conjoined                 *)
(* PROOF SKETCH: elim: n => //= n IH; rewrite IH /luk_conj; case on the     *)
(* sign of (n.+1)%:R * x - n%:R (leP), then field arithmetic (mulrS,        *)
(* natrD, opprD, addrA...).  In the degenerate branch use that x <= 1       *)
(* forces the next numerator below 0 as well -- both sides collapse to 0.   *)
(* Requires 0 <= x <= 1.                                                     *)
Lemma luk_selfpow x n : luk_range x ->
  selfpow luk_conj x n = Num.max 0 ((n.+1)%:R * x - n%:R).
Proof.
move=> hrange; move: (hrange); rewrite /luk_range !inE => /andP[hx0 hx1].
elim: n => [|n IH] /=; first by rewrite mul1r subr0 max_r.
rewrite IH /luk_conj.
have Hid : n.+2%:R * x - n.+1%:R = (n.+1%:R * x - n%:R) + (x - 1).
  rewrite !mulr_natl mulrS -natr1 opprD !addrA [x + x *+ n.+1]addrC.
  by rewrite -!addrA; congr (_ + _); rewrite addrCA.
rewrite Hid; case: (lerP (n.+1%:R * x - n%:R) 0) => hsgn.
- have h1 : x - 1 <= 0 by rewrite subr_le0.
  have h2 : n.+1%:R * x - n%:R + (x - 1) <= 0.
    by rewrite -[X in _ <= X](addr0 0); apply: lerD.
  by rewrite addr0 (max_l h1) (max_l h2).
- by congr (Num.max 0 _); rewrite [x + _]addrC -addrA.
Qed.

(* the W-window idempotency defect: 1 - 1/W                                 *)
(* PROOF SKETCH: rewrite luk_selfpow //; cdistE.  Two branches:             *)
(*  - (n.+1)%:R * x - n%:R <= 0: |0 - x| = x, and the branch condition      *)
(*    gives x <= n%:R / (n.+1)%:R = 1 - (n.+1)%:R^-1 <= 1 - W%:R^-1         *)
(*    (lef_pV2 / ler_pinv on n.+1 <= W, i.e. n < W).                        *)
(*  - 0 < (n.+1)%:R * x - n%:R: the difference is n%:R * (1 - x), and       *)
(*    x >= n%:R/(n.+1)%:R gives n%:R * (1-x) <= n%:R/(n.+1)%:R              *)
(*    <= 1 - W%:R^-1.                                                        *)
Lemma luk_defect (W : nat) x n : luk_range x -> (0 < W)%N -> (n < W)%N ->
  (cdist (selfpow luk_conj x n) x <= 1 - (W%:R)^-1)%R.
Proof.
move=> hrange hW hnW.
move: (hrange); rewrite /luk_range !inE => /andP[hx0 hx1].
rewrite (luk_selfpow _ hrange) cdistE.
have hn1 : (0 : R) < n.+1%:R by rewrite ltr0Sn.
have hn1' : (n.+1%:R : R) != 0 by rewrite lt0r_neq0.
have Heq : n%:R / n.+1%:R = 1 - n.+1%:R^-1 :> R.
  have -> : n%:R = n.+1%:R - 1 :> R by rewrite -natr1 addrK.
  by rewrite mulrBl divff // mul1r.
have hWinv : (1 - n.+1%:R^-1 : R) <= 1 - W%:R^-1.
  by rewrite lerD2l lerN2 lef_pV2 ?ler_nat // posrE ltr0n.
case: (lerP (n.+1%:R * x - n%:R) 0) => hsgn.
- rewrite sub0r normrN ger0_norm //.
  apply: le_trans hWinv.
  by rewrite -Heq ler_pdivlMr // mulrC -subr_le0.
- have -> : n.+1%:R * x - n%:R - x = n%:R * x - n%:R.
    by rewrite -natr1 mulrDl mul1r addrAC addrK.
  apply: le_trans hWinv.
  rewrite distrC ger0_norm; last first.
    by rewrite subr_ge0 -{2}[n%:R]mulr1 ler_wpM2l // ler0n.
  have h1x : 1 - x <= n.+1%:R^-1.
    by rewrite lerBlDl addrC -lerBlDl -Heq ler_pdivrMr // mulrC ltW // -subr_gt0.
  have -> : n%:R - n%:R * x = n%:R * (1 - x) by rewrite mulrBr mulr1.
  rewrite -Heq mulrC.
  apply: le_trans (_ : n.+1%:R^-1 * n%:R <= _).
    by rewrite ler_wpM2r // ?ler0n.
  by rewrite mulrC.
Qed.

(* Packaged: Lukasiewicz satisfies the reuse theorem's window condition     *)
(* with delta = 1 - 1/W, by the defect builder.                             *)
Lemma luk_window_bound (W : nat) (x : R) (s : seq R) : (0 < W)%N ->
  luk_range x -> all luk_range s -> (size s < W)%N ->
  (cdist (opfold luk_conj x s) (minS x s) <= 1 - (W%:R)^-1)%R.
Proof.
move=> W0 hx hs hsz.
apply: (monoid_window_bound (W:=W) luk_conj_monol luk_conj_monor
          luk_conj_submeet) => //.
by move=> y n hy hn; apply: luk_defect.
Qed.

End Lukasiewicz.

(******************************************************************************)
(* Part 5: DL2 -- no finite idempotency defect, hence no reuse bound         *)
(******************************************************************************)

Section DL2.
Variable R : realDomainType.

(* DL2's conjunction is +.  Even on the constant 2-window [x; x] (in        *)
(* sigma = + orientation: satisfaction side x <= 0, where + IS sub-meet     *)
(* and monotone -- a perfectly good "affine" monoidal operator), its        *)
(* distance to the strict minimum is |x|, unbounded on the range.  So no    *)
(* finite delta discharges the window condition: DL2 genuinely fails the    *)
(* reuse conditions, as claimed (and only remarked) in the paper.           *)
(* PROOF SKETCH: given delta, take x := - `|delta| - 1; then                *)
(* |(x + x) - x| = |x| = `|delta| + 1 > delta.                              *)
Lemma dl2_no_finite_defect :
  ~ (exists delta : R, forall x : R, (x <= 0)%R ->
       (cdist (selfpow (fun a b : R => a + b) x 1) x <= delta)%R).
Proof.
move=> [delta hdelta].
have hx : - (1 + `|delta|) <= 0.
  by rewrite oppr_le0 addr_ge0 // ler01.
have := hdelta _ hx.
rewrite /= cdistE addrK normrN ger0_norm; last by rewrite addr_ge0 // ler01.
move=> hcontra.
have h1 : delta <= `|delta| by rewrite ler_norm.
have h2 : `|delta| < 1 + `|delta| by rewrite ltrDr ltr01.
have := le_lt_trans (le_trans hcontra h1) h2.
by rewrite ltxx.
Qed.

End DL2.
