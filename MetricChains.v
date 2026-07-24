(******************************************************************************)
(* Metric chains: the value algebra of the residuated-lattice reuse theorem  *)
(*                                                                            *)
(* This file provides the foundation for the abstract ("residuated-lattice") *)
(* recast of the paper's Reuse theorem (see ReuseDefect.v):                  *)
(*                                                                            *)
(* 1. An HB structure [metricChainType R d]: a total order (mathcomp's       *)
(*    Order.Total) equipped with an R-valued distance (R : numDomainType)    *)
(*    that is symmetric, triangular, reflexive-zero and *order-convex*       *)
(*    (the distance grows along the chain).  Order-convexity is what makes   *)
(*    Birkhoff non-expansiveness of min/max provable, and it is the only     *)
(*    interaction between the metric and the order that the reuse theorem    *)
(*    needs.  A generic instance makes every realDomainType a metric chain   *)
(*    with cdist x y = `|x - y|.                                             *)
(*                                                                            *)
(* 2. Head-form min/max folds over nonempty windows (minS x s = minimum of   *)
(*    x :: s), their membership/bound lemmas, and their non-expansiveness    *)
(*    under pointwise distance bounds (all2-based, no default elements).     *)
(*                                                                            *)
(* 3. Involution theory: an antitone involutive isometry (the De Morgan      *)
(*    negation of the value algebra: -x for STL, 1-x for Kleene-Zadeh).      *)
(*                                                                            *)
(* 4. The *monoidal instance builder* (Section DefectOfMonoid): a monotone,  *)
(*    sub-meet ("integral") binary operator whose W-th idempotency defect    *)
(*    is bounded by delta satisfies the reuse theorem's window-deviation     *)
(*    condition with that same delta.  Substructurally: quantitative         *)
(*    contraction-admissibility.  Dually for join.                           *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(******************************************************************************)
(* Part 1: the HB structure                                                   *)
(******************************************************************************)

HB.mixin Record isMetricChain (R : numDomainType) (d : Order.disp_t) T
    of Order.Total d T := {
  cdist : T -> T -> R;
  cdist_ge0 : forall x y, (0 <= cdist x y)%R;
  cdistC : forall x y, cdist x y = cdist y x;
  cdist_triangle : forall x y z, (cdist x z <= cdist x y + cdist y z)%R;
  cdistxx : forall x, cdist x x = 0%R;
  cdist_convexl : forall x y z : T, x <= y -> y <= z ->
    (cdist x y <= cdist x z)%R;
  cdist_convexr : forall x y z : T, x <= y -> y <= z ->
    (cdist y z <= cdist x z)%R
}.

#[short(type="metricChainType")]
HB.structure Definition MetricChain (R : numDomainType) (d : Order.disp_t) :=
  { T of Order.Total d T & isMetricChain R d T }.

(* Every realDomainType is a metric chain for the absolute-value distance.   *)
Section RealDist.
Variable R : realDomainType.
Implicit Types x y z : R.

Lemma rdist_ge0 x y : (0 <= `|x - y|)%R.
Proof. exact: normr_ge0. Qed.

Lemma rdistC x y : `|x - y| = `|y - x|.
Proof. exact: distrC. Qed.

Lemma rdist_triangle x y z : (`|x - z| <= `|x - y| + `|y - z|)%R.
Proof. exact: ler_distD. Qed.

Lemma rdistxx x : `|x - x| = 0%R.
Proof. by rewrite subrr normr0. Qed.

Lemma rdist_convexl x y z : (x <= y)%R -> (y <= z)%R ->
  (`|x - y| <= `|x - z|)%R.
Proof.
move=> h1 h2; have h3 := le_trans h1 h2.
rewrite distrC (distrC x z) !ger0_norm ?subr_ge0 //.
by rewrite lerD2r.
Qed.

Lemma rdist_convexr x y z : (x <= y)%R -> (y <= z)%R ->
  (`|y - z| <= `|x - z|)%R.
Proof.
move=> h1 h2; have h3 := le_trans h1 h2.
rewrite (distrC y z) (distrC x z) !ger0_norm ?subr_ge0 //.
by rewrite lerD2l lerN2.
Qed.

End RealDist.

(* The instance is keyed on the sort of a realDomainType, i.e. it applies    *)
(* whenever the carrier is *presented* as a realDomainType.  This is a       *)
(* non-forgetful-inheritance instance (the metric is derived data), which    *)
(* is intended: no competing MetricChain path on real domains exists.        *)
#[non_forgetful_inheritance]
HB.instance Definition _ (R : realDomainType) :=
  isMetricChain.Build R ring_display R
    (@rdist_ge0 R) (@rdistC R) (@rdist_triangle R) (@rdistxx R)
    (@rdist_convexl R) (@rdist_convexr R).

(* The same instance keyed on the stronger structures, so that cdist also    *)
(* fires when the carrier is presented as a realFieldType (the generic       *)
(* instance above is keyed on Num.RealDomain.sort only).                     *)
#[non_forgetful_inheritance]
HB.instance Definition _ (R : realFieldType) :=
  isMetricChain.Build R ring_display R
    (@rdist_ge0 R) (@rdistC R) (@rdist_triangle R) (@rdistxx R)
    (@rdist_convexl R) (@rdist_convexr R).

(* Sanity: cdist computes to the absolute distance on any realDomainType.    *)
Section RealDistSanity.
Variable R : realDomainType.
Lemma cdistE (x y : R) : cdist x y = `|x - y|. Proof. by []. Qed.
End RealDistSanity.

(******************************************************************************)
(* Part 2: derived metric-chain theory                                        *)
(******************************************************************************)

Section MetricChainTheory.
Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.
Implicit Types (x y z a b : L) (e : R).

(* Betweenness bound: if y sits between x and z, its distance to either end  *)
(* is bounded by cdist x z.  Direct from convexity.                          *)

(* Birkhoff non-expansiveness of binary min/max, from order-convexity.       *)
(* PROOF SKETCH (dist_min): case: (leP x a) => hxa; case: (leP y b) => hyb   *)
(* replaces the min's in the goal (leP substitutes min/max occurrences).     *)
(* Four cases; the mixed ones (e.g. min = x and min = b) split again on      *)
(* le_total x b and close with cdist_convexl / cdist_convexr and cdistC:     *)
(*   x <= b: then x <= b <= y (since b < y), so cdist x b <= cdist x y.      *)
(*   b <= x: then b <= x <= a, so cdist x b = cdist b x <= cdist b a.        *)
Lemma dist_min x y a b e :
  (cdist x y <= e)%R -> (cdist a b <= e)%R ->
  (cdist (Order.min x a) (Order.min y b) <= e)%R.
Proof.
move=> hxy hab.
case: (leP x a) => hxa; case: (leP y b) => hyb.
- exact: hxy.
- case/orP: (le_total x b) => hxb.
    apply: le_trans hxy. apply: cdist_convexl hxb (ltW hyb).
  rewrite cdistC. apply: le_trans hab. rewrite (cdistC a b).
  apply: cdist_convexl hxb hxa.
- case/orP: (le_total a y) => hay.
    apply: le_trans hab. apply: cdist_convexl hay hyb.
  rewrite cdistC. apply: le_trans hxy. rewrite (cdistC x y).
  apply: cdist_convexl hay (ltW hxa).
- exact: hab.
Qed.

Lemma dist_max x y a b e :
  (cdist x y <= e)%R -> (cdist a b <= e)%R ->
  (cdist (Order.max x a) (Order.max y b) <= e)%R.
Proof.
move=> hxy hab.
case: (leP x a) => hxa; case: (leP y b) => hyb.
- exact: hab.
- case/orP: (le_total a y) => hay.
    apply: le_trans hxy. apply: cdist_convexr hxa hay.
  rewrite cdistC. apply: le_trans hab. rewrite (cdistC a b).
  apply: cdist_convexr (ltW hyb) hay.
- case/orP: (le_total x b) => hxb.
    apply: le_trans hab. apply: cdist_convexr (ltW hxa) hxb.
  rewrite cdistC. apply: le_trans hxy. rewrite (cdistC x y).
  apply: cdist_convexr hyb hxb.
- exact: hxy.
Qed.

End MetricChainTheory.

(******************************************************************************)
(* Part 3: head-form min/max folds over nonempty windows                      *)
(*                                                                            *)
(* minS x s is the minimum of the nonempty window x :: s.  The head-form     *)
(* avoids junk default elements entirely: every window of the temporal       *)
(* semantics is nonempty by construction.                                     *)
(******************************************************************************)

Section SeqChain.
Context {disp : Order.disp_t} {T : orderType disp}.
Implicit Types (x y : T) (s : seq T).

Fixpoint minS x s : T :=
  if s is y :: s' then Order.min x (minS y s') else x.

Fixpoint maxS x s : T :=
  if s is y :: s' then Order.max x (maxS y s') else x.

Lemma minS_cons x y s : minS x (y :: s) = Order.min x (minS y s).
Proof. by []. Qed.

Lemma maxS_cons x y s : maxS x (y :: s) = Order.max x (maxS y s).
Proof. by []. Qed.

(* The minimum is dominated by every window entry.                           *)
(* PROOF SKETCH: elim: s x with in_cons case analysis; ge_min/le_min.        *)
Lemma minS_le x s y : y \in x :: s -> minS x s <= y.
Proof.
elim: s x => [|z s IH] x /=.
  by rewrite mem_seq1 => /eqP ->.
rewrite in_cons ge_min => /orP[/eqP -> | hin].
  by rewrite lexx.
by rewrite IH ?orbT.
Qed.

Lemma maxS_ge x s y : y \in x :: s -> y <= maxS x s.
Proof.
elim: s x => [|z s IH] x /=.
  by rewrite mem_seq1 => /eqP ->.
rewrite in_cons le_max => /orP[/eqP -> | hin].
  by rewrite lexx.
by rewrite IH ?orbT.
Qed.

(* The minimum is attained (chains only).                                    *)
(* PROOF SKETCH: elim: s x; case: (leP x (minS y s')) substitutes the min.   *)
Lemma minS_mem x s : minS x s \in x :: s.
Proof.
elim: s x => [|y s' IH] x /=.
  by rewrite mem_head.
case: (leP x (minS y s')) => h.
  by rewrite mem_head.
by rewrite in_cons IH ?orbT.
Qed.

Lemma maxS_mem x s : maxS x s \in x :: s.
Proof.
elim: s x => [|y s' IH] x /=.
  by rewrite mem_head.
case: (leP x (maxS y s')) => h.
  by rewrite in_cons IH ?orbT.
by rewrite mem_head.
Qed.

End SeqChain.

(* Pointwise non-expansiveness of the window reductions: the seq-level form  *)
(* of the paper's Lemma "Non-expansiveness of strict reductions".            *)
Section SeqChainDist.
Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.
Implicit Types (x y : L) (u v : seq L) (e : R).

(* PROOF SKETCH: elim: u v => [|a u IH] [|b v] //= with all2 destructing;    *)
(* base: the head bound; step: dist_min + IH.                                *)
Lemma minS_dist2 e x y u v :
  (cdist x y <= e)%R ->
  all2 (fun a b => cdist a b <= e)%R u v ->
  (cdist (minS x u) (minS y v) <= e)%R.
Proof.
elim: u v x y => [|a u IH] [|b v] x y //= hxy.
move=> /andP[hab h2].
by apply: dist_min hxy (IH _ _ _ hab h2).
Qed.

Lemma maxS_dist2 e x y u v :
  (cdist x y <= e)%R ->
  all2 (fun a b => cdist a b <= e)%R u v ->
  (cdist (maxS x u) (maxS y v) <= e)%R.
Proof.
elim: u v x y => [|a u IH] [|b v] x y //= hxy.
move=> /andP[hab h2].
by apply: dist_max hxy (IH _ _ _ hab h2).
Qed.

End SeqChainDist.

(* Generic helper: pointwise conditions on two maps over the same index      *)
(* list, as an all2.                                                          *)
(* PROOF SKETCH: elim: l => //= i l IH /andP[-> /IH].                        *)
Lemma all2_map (T1 T2 T3 : Type) (P : T2 -> T3 -> bool)
    (f : T1 -> T2) (g : T1 -> T3) (l : seq T1) :
  all (fun i => P (f i) (g i)) l -> all2 P (map f l) (map g l).
Proof.
by elim: l => //= i l IH /andP[-> /IH].
Qed.

(******************************************************************************)
(* Part 4: involution theory                                                  *)
(*                                                                            *)
(* The De Morgan negation of the value algebra is an antitone involutive     *)
(* isometry.  It is a section parameter, NOT part of the HB structure: a     *)
(* single carrier supports several involutions (-x and 1-x on the reals),    *)
(* so it cannot be canonical per type.                                        *)
(******************************************************************************)

Section InvolutionTheory.
Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.
Variable ineg : L -> L.
Hypothesis inegK : involutive ineg.
Hypothesis ineg_anti : {homo ineg : x y /~ x <= y}.
Hypothesis ineg_isom : forall x y, cdist (ineg x) (ineg y) = cdist x y.

Lemma ineg_inj : injective ineg.
Proof. exact: inv_inj. Qed.

(* PROOF SKETCH: antitone + injective on a total order.  For <=: one         *)
(* direction is ineg_anti; the other applies ineg_anti to ineg x <= ineg y   *)
(* and rewrites with inegK.  For <: use lt_def / le + injectivity.           *)
Lemma ineg_le (x y : L) : (ineg x <= ineg y) = (y <= x).
Proof.
apply/idP/idP => h.
  by have := ineg_anti h; rewrite !inegK.
exact: ineg_anti h.
Qed.

Lemma ineg_lt (x y : L) : (ineg x < ineg y) = (y < x).
Proof.
by rewrite !lt_def ineg_le (inj_eq ineg_inj) eq_sym.
Qed.

End InvolutionTheory.

(******************************************************************************)
(* Part 5: the monoidal instance builder                                      *)
(*                                                                            *)
(* A binary operator op that is monotone in both arguments and sub-meet      *)
(* ("integral": op x y <= min x y) on a working range has its window         *)
(* deviation from the strict minimum controlled by its *idempotency defect*  *)
(*   selfpow x n = x (.) x (.) ... (.) x   (n+1 copies)                      *)
(* via the sandwich   selfpow (minS w) (size w - 1) <= fold op w <= minS w   *)
(* and order-convexity of the distance.  Substructural reading: op admits    *)
(* contraction up to delta on windows of size <= W.                          *)
(******************************************************************************)

Section DefectOfMonoid.
Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.
Variables (op : L -> L -> L) (inrange : pred L).

(* fold of op over a nonempty window, head form (same shape as minS)         *)
Fixpoint opfold (x : L) (s : seq L) : L :=
  if s is y :: s' then op x (opfold y s') else x.

(* n-fold self-application: selfpow x n = op x (op x (... x)) with n op's    *)
Fixpoint selfpow (x : L) (n : nat) : L :=
  if n is m.+1 then op x (selfpow x m) else x.

Hypothesis op_monol : forall y, {homo op^~ y : x x' / x <= x'}.
Hypothesis op_monor : forall x, {homo op x : y y' / y <= y'}.
Hypothesis op_submeet : forall x y, inrange x -> inrange y ->
  op x y <= Order.min x y.
Hypothesis op_range : forall x y, inrange x -> inrange y ->
  inrange (op x y).

(* range closure of the fold *)
(* PROOF SKETCH: elim: s x => //= with op_range.                             *)
Lemma opfold_range x s : inrange x -> all inrange s ->
  inrange (opfold x s).
Proof.
elim: s x => [|y s' IH] x //= hx /andP[hy hs].
by apply: op_range hx (IH _ hy hs).
Qed.

(* upper half of the sandwich: the fold is below the strict minimum          *)
(* PROOF SKETCH: elim: s x; cons case: op x (opfold y s') <=                 *)
(*   op x (minS y s')   [op_monor + IH; needs minS y s' \in inrange via      *)
(*                       minS_mem + allP]                                     *)
(*   <= min x (minS y s')  [op_submeet].                                     *)
Lemma opfold_le_minS x s : inrange x -> all inrange s ->
  opfold x s <= minS x s.
Proof.
elim: s x => [|y s' IH] x //= hx /andP[hy hs].
have hmin : inrange (minS y s').
  by move: (minS_mem y s'); apply/allP; rewrite /= hy hs.
apply: le_trans (op_submeet hx hmin).
apply: op_monor. exact: IH.
Qed.

(* lower half: the fold dominates the self-power of any lower bound          *)
(* PROOF SKETCH: elim: s x m => //=; cons: selfpow m (size s').+1 =          *)
(* op m (selfpow m (size s')) <= op x (opfold y s') by op_monol/op_monor+IH. *)
Lemma opfold_ge_selfpow (m x : L) s : m <= x -> all (fun z => m <= z) s ->
  selfpow m (size s) <= opfold x s.
Proof.
elim: s x => [|y s' IH] x //= hmx /andP[hmy hs].
apply: le_trans.
  apply: (op_monol (selfpow m (size s')) hmx).
apply: op_monor. exact: IH.
Qed.

(* The window-deviation bound from the idempotency defect.  This is the      *)
(* lemma that discharges the reuse theorem's (R3) for any monoidal DL.       *)
(* PROOF SKETCH: set m := minS x s; sandwich selfpow m (size s) <= opfold    *)
(* <= m (previous two lemmas, minS_le for the all-bound); then               *)
(* cdist (opfold x s) m <= cdist (selfpow m (size s)) m  [cdist_convexr]     *)
(* <= delta [defect hypothesis; m \in inrange via minS_mem + allP].          *)
Lemma monoid_window_bound (W : nat) (delta : R) :
  (forall x n, inrange x -> (n < W)%N ->
    (cdist (selfpow x n) x <= delta)%R) ->
  forall x s, inrange x -> all inrange s -> (size s < W)%N ->
  (cdist (opfold x s) (minS x s) <= delta)%R.
Proof.
move=> Hdef x s hx hs hsz.
set m := minS x s.
have hmem : m \in x :: s by apply: minS_mem.
have hmr : inrange m.
  by move: hmem; apply/allP; rewrite /= hx hs.
have hmx : m <= x by apply: minS_le; rewrite mem_head.
have hms : all (fun z => m <= z) s.
  by apply/allP => z hz; apply: minS_le; rewrite in_cons hz orbT.
have hlo : selfpow m (size s) <= opfold x s by apply: opfold_ge_selfpow.
have hhi : opfold x s <= m by apply: opfold_le_minS.
apply: le_trans (Hdef m (size s) hmr hsz).
apply: cdist_convexr hlo hhi.
Qed.

End DefectOfMonoid.

(* Dual builder: a super-join operator ("co-integral": op x y >= max x y)    *)
(* controls the deviation from the strict maximum.  Same proofs, dualized.   *)
Section DefectOfMonoidDual.
Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.
Variables (op : L -> L -> L) (inrange : pred L).

Hypothesis op_monol : forall y, {homo op^~ y : x x' / x <= x'}.
Hypothesis op_monor : forall x, {homo op x : y y' / y <= y'}.
Hypothesis op_superjoin : forall x y, inrange x -> inrange y ->
  Order.max x y <= op x y.
Hypothesis op_range : forall x y, inrange x -> inrange y ->
  inrange (op x y).

Lemma opfold_ge_maxS x s : inrange x -> all inrange s ->
  maxS x s <= opfold op x s.
Proof.
elim: s x => [|y s' IH] x //= hx /andP[hy hs].
have hmax : inrange (maxS y s').
  by move: (maxS_mem y s'); apply/allP; rewrite /= hy hs.
apply: le_trans (op_superjoin hx hmax) _.
apply: op_monor. exact: IH.
Qed.

Lemma opfold_le_selfpow (m x : L) s : x <= m -> all (fun z => z <= m) s ->
  opfold op x s <= selfpow op m (size s).
Proof.
elim: s x => [|y s' IH] x //= hxm /andP[hym hs].
apply: le_trans.
  apply: (op_monol (opfold op y s') hxm).
apply: op_monor. exact: IH.
Qed.

Lemma monoid_window_bound_max (W : nat) (delta : R) :
  (forall x n, inrange x -> (n < W)%N ->
    (cdist (selfpow op x n) x <= delta)%R) ->
  forall x s, inrange x -> all inrange s -> (size s < W)%N ->
  (cdist (opfold op x s) (maxS x s) <= delta)%R.
Proof.
move=> Hdef x s hx hs hsz.
set M := maxS x s.
have hmem : M \in x :: s by apply: maxS_mem.
have hMr : inrange M.
  by move: hmem; apply/allP; rewrite /= hx hs.
have hxM : x <= M by apply: maxS_ge; rewrite mem_head.
have hsM : all (fun z => z <= M) s.
  by apply/allP => z hz; apply: maxS_ge; rewrite in_cons hz orbT.
have hhi : opfold op x s <= selfpow op M (size s) by apply: opfold_le_selfpow.
have hlo : M <= opfold op x s by apply: opfold_ge_maxS.
apply: le_trans (Hdef M (size s) hMr hsz).
rewrite (cdistC (opfold op x s) M) (cdistC (selfpow op M (size s)) M).
apply: cdist_convexl hlo hhi.
Qed.

End DefectOfMonoidDual.
