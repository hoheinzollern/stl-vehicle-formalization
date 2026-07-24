(******************************************************************************)
(* The Reuse theorem over an abstract metric chain                            *)
(*                                                                            *)
(* This is the "residuated-lattice" recast of the paper's Reuse theorem      *)
(* (cf. ReuseTheorem.v for the concrete real-valued development).  The       *)
(* value algebra is an abstract metric chain L (MetricChain.v); the          *)
(* reference semantics rhoL interprets bounded STL into L's *lattice         *)
(* reduct* (min / max / an antitone involutive isometry ineg with fixpoint   *)
(* theta); a DL supplies window reductions conjL / disjL whose deviation     *)
(* from the strict min / max is bounded by delta_conj / delta_disj on        *)
(* in-range windows of size <= Wmax (discharged for monoidal DLs by the      *)
(* defect builder of MetricChain.v).  The theorem: the DL interpretation     *)
(* is within  B = delta_atom + delta_conj *+ d/\ + delta_disj *+ d\/  of     *)
(* the reference, and a value separated from theta by more than B decides    *)
(* satisfaction.                                                              *)
(*                                                                            *)
(* Differences from ReuseTheorem.v, all deliberate:                          *)
(*  - no sign sigma: a sigma = - DL is an instance over the dual/flipped     *)
(*    orientation (the involution absorbs the sign);                          *)
(*  - no masked-scan padding, hence no eps_top/eps_bot: this formalizes the  *)
(*    paper's Section 5.1 semantics with exact windows (the padding slack    *)
(*    is a runtime artefact, treated in the concrete development);           *)
(*  - the satisfaction threshold is theta (the involution's fixpoint):       *)
(*    0 for STL's -x, 1/2 for Kleene-Zadeh / Lukasiewicz's 1-x;              *)
(*  - the boolean part is stated by separation: a DL value whose entire      *)
(*    closed B-ball lies above theta certifies satisfaction (on real chains  *)
(*    this is literally  theta + B < value ; see ReuseInstances.v).          *)
(*                                                                            *)
(* The formula syntax (form), window (win), boolean semantics (sat) and      *)
(* depth/window measures (dconj, ddisj, maxwin) are shared with              *)
(* ReuseTheorem.v.                                                            *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Require Import MetricChains BoundedSTL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Section ReuseDefect.

Context {R : numDomainType} {d : Order.disp_t} {L : metricChainType R d}.

Variable V : Type.                       (* signal value space *)
Notation signal := (nat -> V).

(* ---------------------------------------------------------------------- *)
(* The abstract non-temporal layer, as in ReuseTheorem.v, but L-valued     *)
(* and thresholded at theta.                                               *)

Variable NT : Type.
Variable nt_sat : NT -> signal -> nat -> Prop.
Variable nt_rho : NT -> signal -> nat -> L.

(* the De Morgan involution of the value algebra and its fixpoint          *)
Variable ineg : L -> L.
Variable theta : L.
Hypothesis inegK : involutive ineg.
Hypothesis ineg_anti : {homo ineg : x y /~ x <= y}.
Hypothesis ineg_isom : forall x y, cdist (ineg x) (ineg y) = cdist x y.
Hypothesis ineg_theta : ineg theta = theta.

Hypothesis nt_rho_pos : forall p s t, theta < nt_rho p s t -> nt_sat p s t.
Hypothesis nt_rho_neg : forall p s t, nt_rho p s t < theta -> ~ nt_sat p s t.

(* ---------------------------------------------------------------------- *)
(* Reference semantics: interpretation into the lattice reduct of L (the  *)
(* DL's "Godelization").  Windows are nonempty by construction and taken  *)
(* in head form: the window of [a, b] at time t is                        *)
(*    f (t+a)  ::  [seq f (t+i) | i <- iota a.+1 (b - a)]                 *)
(* which is exactly [seq f (t+i) | i <- win a b] (win a b = iota a        *)
(* (b-a).+1 unfolds to a :: iota a.+1 (b - a) definitionally).            *)

Fixpoint rhoL (phi : form NT) (s : signal) (t : nat) : L :=
  match phi with
  | FAtom p => nt_rho p s t
  | FNeg psi => ineg (rhoL psi s t)
  | FGlobally a b psi =>
      minS (rhoL psi s (t + a))
           [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)]
  | FFinally a b psi =>
      maxS (rhoL psi s (t + a))
           [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)]
  | FUntil a b psi chi =>
      let uw := fun j => minS (rhoL chi s (t + j))
                              [seq rhoL psi s (t + i) | i <- iota 0 j] in
      maxS (uw a) [seq uw j | j <- iota a.+1 (b - a)]
  end.

(* One-step equations (rewrite with these; do NOT use bare /= on goals     *)
(* containing rhoL/evalL applied to a constructor -- simpl over-unfolds    *)
(* win/iota/minS).                                                          *)
Lemma rhoL_negE psi s t : rhoL (FNeg psi) s t = ineg (rhoL psi s t).
Proof. by []. Qed.

Lemma rhoL_GE a b psi s t :
  rhoL (FGlobally a b psi) s t
  = minS (rhoL psi s (t + a))
         [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)].
Proof. by []. Qed.

Lemma rhoL_FE a b psi s t :
  rhoL (FFinally a b psi) s t
  = maxS (rhoL psi s (t + a))
         [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)].
Proof. by []. Qed.

Lemma rhoL_UE a b psi chi s t :
  rhoL (FUntil a b psi chi) s t
  = maxS (minS (rhoL chi s (t + a))
               [seq rhoL psi s (t + i) | i <- iota 0 a])
         [seq minS (rhoL chi s (t + j))
               [seq rhoL psi s (t + i) | i <- iota 0 j]
         | j <- iota a.+1 (b - a)].
Proof. by []. Qed.

(* window membership: i \in win a b  <->  head-or-tail of the head form   *)
Lemma win_head a b : win a b = a :: iota a.+1 (b - a).
Proof. by []. Qed.

(* ---------------------------------------------------------------------- *)
(* Sign-soundness of the reference semantics w.r.t. the threshold theta:  *)
(* strictly above theta implies sat, strictly below implies ~ sat.  The   *)
(* negation case uses that ineg is a strictly antitone involution fixing  *)
(* theta (ineg_lt from MetricChain.v).                                     *)
(*                                                                          *)
(* PROOF SKETCH: as rho_sound in ReuseTheorem.v, with:                     *)
(*  - 0 replaced by theta;                                                 *)
(*  - rmin_le/rmin_mem replaced by minS_le/minS_mem (note their cons       *)
(*    membership statements match win_head);                               *)
(*  - the FNeg case: theta < ineg r iff r < theta via ineg_lt + inegK +    *)
(*    ineg_theta;                                                          *)
(*  - membership in the mapped window via mapP/map_f and win_head,         *)
(*    mem_iota for the until inner windows.                                *)
Lemma rhoL_sound phi s t :
  (theta < rhoL phi s t -> sat nt_sat phi s t) /\
  (rhoL phi s t < theta -> ~ sat nt_sat phi s t).
Proof.
move: t; elim: phi => [p|psi IH|a b psi IH|a b psi IH|a b psi IHp chi IHc] t; split.
- exact: nt_rho_pos.
- exact: nt_rho_neg.
- rewrite rhoL_negE -[theta in theta < _]ineg_theta (ineg_lt inegK ineg_anti).
  exact: (proj2 (IH t)).
- rewrite rhoL_negE -[X in _ < X]ineg_theta (ineg_lt inegK ineg_anti) => /(proj1 (IH t)) hs hns; exact: hns hs.
- rewrite rhoL_GE => h i hi; apply: (proj1 (IH (t + i)%N)).
  apply: lt_le_trans h _; apply: minS_le.
  rewrite -[rhoL psi s (t + a) :: _]/([seq rhoL psi s (t + j) | j <- win a b]).
  exact: map_f hi.
- rewrite rhoL_GE => h hall.
  have hmem : minS (rhoL psi s (t + a)) [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)]
    \in [seq rhoL psi s (t + j) | j <- win a b].
    by rewrite win_head; apply: minS_mem.
  case/mapP: hmem => i hi heq; apply: (proj2 (IH (t + i)%N)) _ (hall i hi); by rewrite -heq.
- rewrite rhoL_FE => h.
  have hmem : maxS (rhoL psi s (t + a)) [seq rhoL psi s (t + i) | i <- iota a.+1 (b - a)]
    \in [seq rhoL psi s (t + j) | j <- win a b] by rewrite win_head; apply: maxS_mem.
  case/mapP: hmem => i hi heq.
  exists i => //; apply: (proj1 (IH (t + i)%N)); by rewrite -heq.
- rewrite rhoL_FE => h [i hi hsat].
  apply: (proj2 (IH (t + i)%N)) _ hsat.
  apply: le_lt_trans h; apply: maxS_ge.
  rewrite -[rhoL psi s (t + a) :: _]/([seq rhoL psi s (t + j) | j <- win a b]).
  exact: map_f hi.
- rewrite rhoL_UE => h.
  have hmem : maxS (minS (rhoL chi s (t + a)) [seq rhoL psi s (t + i) | i <- iota 0 a])
     [seq minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j] | j <- iota a.+1 (b - a)]
     \in [seq minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j] | j <- win a b]
     by rewrite win_head; apply: maxS_mem.
  case/mapP: hmem => j hj heq.
  have h0 : theta < minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j] by rewrite -heq.
  exists j => //; split.
  + apply: (proj1 (IHc (t + j)%N)).
    apply: lt_le_trans h0 _; apply: minS_le; exact: mem_head.
  + move=> i hij; apply: (proj1 (IHp (t + i)%N)).
    apply: lt_le_trans h0 _; apply: minS_le.
    rewrite in_cons; apply/orP; right.
    apply: (map_f (fun k => rhoL psi s (t + k))).
    by rewrite mem_iota add0n hij andbT.
- rewrite rhoL_UE => h [j hj [hchi hpsi]].
  have hin : minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j] < theta.
    apply: le_lt_trans h; apply: maxS_ge.
    rewrite -[minS (rhoL chi s (t + a)) _ :: _]/([seq minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j] | j <- win a b]).
    exact: (map_f (fun j => minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j]) hj).
  have := minS_mem (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j].
  rewrite in_cons => /orP[/eqP heq | /mapP[i hi heq]].
  + by apply: (proj2 (IHc (t + j)%N)) _ hchi; rewrite -heq.
  + move: hi; rewrite mem_iota add0n => /andP[_ hij].
    apply: (proj2 (IHp (t + i)%N)) _ (hpsi i hij); by rewrite -heq.
Qed.

(* ---------------------------------------------------------------------- *)
(* The host DL: window reductions, negation, working range, deviation     *)
(* constants.  For a monoidal DL (op monotone + sub-meet), conjL is       *)
(* fun w => opfold op (head w) (behead w) and delta_conj is its           *)
(* idempotency defect (MetricChain.v, monoid_window_bound).               *)

Variable conjL : seq L -> L.   (* applied to nonempty windows only *)
Variable disjL : seq L -> L.
Variable negL : L -> L.
Variable inrange : pred L.
Variable Wmax : nat.
Variables delta_conj delta_disj delta_atom : R.

Hypothesis delta_conj_ge0 : (0 <= delta_conj)%R.
Hypothesis delta_disj_ge0 : (0 <= delta_disj)%R.

(* (R3): deviation from the strict reductions on in-range windows.        *)
Hypothesis conjL_strict : forall x s, inrange x -> all inrange s ->
  (size s < Wmax)%N -> (cdist (conjL (x :: s)) (minS x s) <= delta_conj)%R.
Hypothesis disjL_strict : forall x s, inrange x -> all inrange s ->
  (size s < Wmax)%N -> (cdist (disjL (x :: s)) (maxS x s) <= delta_disj)%R.

(* (R4): the DL negation is the algebra's involution.                     *)
Hypothesis negL_E : forall x, negL x = ineg x.

(* working-range closure *)
Hypothesis conjL_range : forall x s, inrange x -> all inrange s ->
  inrange (conjL (x :: s)).
Hypothesis disjL_range : forall x s, inrange x -> all inrange s ->
  inrange (disjL (x :: s)).
Hypothesis ineg_range : forall x, inrange x -> inrange (ineg x).

(* the DL's non-temporal fragment and its atom deviation                  *)
Variable nt_evalL : NT -> signal -> nat -> L.
Hypothesis nt_evalL_range : forall p s t, inrange (nt_evalL p s t).
Hypothesis nt_evalL_atom : forall p s t,
  (cdist (nt_evalL p s t) (nt_rho p s t) <= delta_atom)%R.

(* ---------------------------------------------------------------------- *)
(* The DL interpretation of bounded STL (paper Section 5.1, exact          *)
(* windows).                                                                *)

Fixpoint evalL (phi : form NT) (s : signal) (t : nat) : L :=
  match phi with
  | FAtom p => nt_evalL p s t
  | FNeg psi => negL (evalL psi s t)
  | FGlobally a b psi =>
      conjL (evalL psi s (t + a)
             :: [seq evalL psi s (t + i) | i <- iota a.+1 (b - a)])
  | FFinally a b psi =>
      disjL (evalL psi s (t + a)
             :: [seq evalL psi s (t + i) | i <- iota a.+1 (b - a)])
  | FUntil a b psi chi =>
      let uw := fun j => conjL (evalL chi s (t + j)
                                :: [seq evalL psi s (t + i) | i <- iota 0 j]) in
      disjL (uw a :: [seq uw j | j <- iota a.+1 (b - a)])
  end.

Lemma evalL_negE psi s t : evalL (FNeg psi) s t = negL (evalL psi s t).
Proof. by []. Qed.

Lemma evalL_GE a b psi s t :
  evalL (FGlobally a b psi) s t
  = conjL (evalL psi s (t + a)
           :: [seq evalL psi s (t + i) | i <- iota a.+1 (b - a)]).
Proof. by []. Qed.

Lemma evalL_FE a b psi s t :
  evalL (FFinally a b psi) s t
  = disjL (evalL psi s (t + a)
           :: [seq evalL psi s (t + i) | i <- iota a.+1 (b - a)]).
Proof. by []. Qed.

Lemma evalL_UE a b psi chi s t :
  evalL (FUntil a b psi chi) s t
  = disjL (conjL (evalL chi s (t + a)
                  :: [seq evalL psi s (t + i) | i <- iota 0 a])
           :: [seq conjL (evalL chi s (t + j)
                          :: [seq evalL psi s (t + i) | i <- iota 0 j])
              | j <- iota a.+1 (b - a)]).
Proof. by []. Qed.

(* all DL values stay in the working range                                *)
(* PROOF SKETCH: as evalL_range in ReuseTheorem.v: induction with the     *)
(* equation lemmas, conjL_range/disjL_range/ineg_range (+ negL_E), and    *)
(* allP => z /mapP[i hi ->] for the window tails.                         *)
Lemma evalL_inrange phi s t : inrange (evalL phi s t).
Proof.
move: t; elim: phi => [p|psi IH|a b psi IH|a b psi IH|a b psi IHp chi IHc] t.
- exact: nt_evalL_range.
- by rewrite evalL_negE negL_E; apply: ineg_range.
- rewrite evalL_GE; apply: conjL_range; first exact: IH.
  by apply/allP => z /mapP[i hi ->]; exact: IH.
- rewrite evalL_FE; apply: disjL_range; first exact: IH.
  by apply/allP => z /mapP[i hi ->]; exact: IH.
- rewrite evalL_UE; apply: disjL_range.
  + apply: conjL_range; first exact: IHc.
    by apply/allP => w /mapP[i hi ->]; exact: IHp.
  + apply/allP => z /mapP[j hj ->]; apply: conjL_range; first exact: IHc.
    by apply/allP => w /mapP[i hi ->]; exact: IHp.
Qed.

(* ---------------------------------------------------------------------- *)
(* The bound B and its recurrences.                                        *)

Definition Bdef (dw dv : nat) : R :=
  delta_atom + delta_conj *+ dw + delta_disj *+ dv.

Lemma Bdef00 : Bdef 0 0 = delta_atom.
Proof. by rewrite /Bdef !mulr0n !addr0. Qed.

(* PROOF SKETCH: rewrite /Bdef mulrS addrCA -addrA  (conj) and             *)
(* rewrite /Bdef mulrS addrCA  (disj); check the rewrite targets with      *)
(* idtac if they drift.                                                    *)
Lemma BdefSconj dw dv : Bdef dw.+1 dv = delta_conj + Bdef dw dv.
Proof. by rewrite /Bdef mulrS addrA [_ + delta_conj]addrC -!addrA. Qed.

Lemma BdefSdisj dw dv : Bdef dw dv.+1 = delta_disj + Bdef dw dv.
Proof. by rewrite /Bdef mulrS addrCA. Qed.

(* PROOF SKETCH: lerD + ler_wpMn2l (note: pass m/n via underscores:        *)
(* exact: ler_wpMn2l delta_conj_ge0 _ _ h -- {homo} exposes explicit       *)
(* binders).                                                               *)
Lemma Bdef_mono dw dv dw' dv' : (dw <= dw')%N -> (dv <= dv')%N ->
  (Bdef dw dv <= Bdef dw' dv')%R.
Proof.
move=> h1 h2; rewrite /Bdef; apply: lerD.
- apply: lerD; first exact: lexx.
  exact: ler_wpMn2l delta_conj_ge0 _ _ h1.
- exact: ler_wpMn2l delta_disj_ge0 _ _ h2.
Qed.

(* ---------------------------------------------------------------------- *)
(* One-step reduction bounds (paper Lemma "one-step", simplified: no       *)
(* padding, single triangle step through the strict reduction of the      *)
(* DL-side window).                                                        *)
(* PROOF SKETCH: le_trans (cdist_triangle _ (minS x u) _);                 *)
(* lerD (conjL_strict ...) (minS_dist2 ...).                               *)
Lemma one_step_conj (e : R) (x y : L) (u v : seq L) :
  inrange x -> all inrange u -> (size u < Wmax)%N ->
  (cdist x y <= e)%R ->
  all2 (fun a b => cdist a b <= e)%R u v ->
  (cdist (conjL (x :: u)) (minS y v) <= delta_conj + e)%R.
Proof.
move=> hx hu hW hxy hall.
apply: le_trans (cdist_triangle _ (minS x u) _) _.
apply: lerD; first exact: conjL_strict.
exact: minS_dist2 hxy hall.
Qed.

Lemma one_step_disj (e : R) (x y : L) (u v : seq L) :
  inrange x -> all inrange u -> (size u < Wmax)%N ->
  (cdist x y <= e)%R ->
  all2 (fun a b => cdist a b <= e)%R u v ->
  (cdist (disjL (x :: u)) (maxS y v) <= delta_disj + e)%R.
Proof.
move=> hx hu hW hxy hall.
apply: le_trans (cdist_triangle _ (maxS x u) _) _.
apply: lerD; first exact: disjL_strict.
exact: maxS_dist2 hxy hall.
Qed.

(* ---------------------------------------------------------------------- *)
(* Theorem "Reuse", quantitative part, abstract form.                     *)
(*                                                                          *)
(* PROOF SKETCH: move: t; elim: phi => ... t hW; per case:                 *)
(*  - FAtom: Bdef00 + nt_evalL_atom (the depth reductions dconj (FAtom p)  *)
(*    etc. are definitional; use [dconj _]/= [ddisj _]/= pattern-simpl     *)
(*    to expose Bdef 0 0 for the rewrite).                                 *)
(*  - FNeg: evalL_negE rhoL_negE negL_E ineg_isom; conversion handles      *)
(*    the depths.                                                          *)
(*  - FGlobally: split hW via [maxwin _]/= geq_max => /andP[hWw hWp];      *)
(*    rewrite evalL_GE rhoL_GE [dconj _]/= [ddisj _]/= BdefSconj;          *)
(*    apply: one_step_conj with:                                           *)
(*      head range: evalL_inrange; tail range: allP => z /mapP[i hi ->];   *)
(*      size: size_map size_iota, b - a < Wmax from hWw ((b-a).+1 <=       *)
(*      maxn _ _ <= Wmax);                                                 *)
(*      head bound: IH; tail all2: all2_map + apply/allP => i _; IH.       *)
(*  - FFinally: dual.                                                      *)
(*  - FUntil: outer one_step_disj; the all2 for the tail needs, for each   *)
(*    j in iota a.+1 (b - a) (hence j <= a + (b - a), mem_iota, so         *)
(*    j < Wmax via maxwin), the inner bound                                *)
(*      cdist (conjL (inner-eval j)) (minS (inner-rho j)) <=               *)
(*        delta_conj + Bdef (maxn ..) (maxn ..)                            *)
(*    by one_step_conj + IHp/IHc + Bdef_mono (leq_maxl/leq_maxr), then     *)
(*    BdefSconj/BdefSdisj to reassemble.  The head of the outer window is  *)
(*    the same bound at j = a.  Suggest a local `have inner : forall j,    *)
(*    (j < Wmax)%N -> cdist ... <= delta_conj + Bdef D1 D2` to avoid       *)
(*    duplicating the argument for head and tail.                          *)
Theorem reuse_quantitative phi s t :
  (maxwin phi <= Wmax)%N ->
  (cdist (evalL phi s t) (rhoL phi s t) <= Bdef (dconj phi) (ddisj phi))%R.
Proof.
move: t; elim: phi => [p|psi IH|a b psi IH|a b psi IH|a b psi IHp chi IHc] t hW.
- by rewrite [dconj _]/= [ddisj _]/= Bdef00; exact: nt_evalL_atom.
- rewrite evalL_negE rhoL_negE negL_E ineg_isom; exact: IH.
- move: hW; rewrite [maxwin _]/= geq_max => /andP[hWw hWp].
  rewrite evalL_GE rhoL_GE [dconj _]/= [ddisj _]/= BdefSconj.
  apply: one_step_conj.
  + exact: evalL_inrange.
  + by apply/allP => z /mapP[i hi ->]; exact: evalL_inrange.
  + by rewrite size_map size_iota.
  + exact: IH.
  + apply: all2_map; apply/allP => i _; exact: IH.
- move: hW; rewrite [maxwin _]/= geq_max => /andP[hWw hWp].
  rewrite evalL_FE rhoL_FE [dconj _]/= [ddisj _]/= BdefSdisj.
  apply: one_step_disj.
  + exact: evalL_inrange.
  + by apply/allP => z /mapP[i hi ->]; exact: evalL_inrange.
  + by rewrite size_map size_iota.
  + exact: IH.
  + apply: all2_map; apply/allP => i _; exact: IH.
- move: hW; rewrite [maxwin _]/= !geq_max => /andP[hWu /andP[hWp hWc]].
  rewrite evalL_UE rhoL_UE [dconj _]/= [ddisj _]/= BdefSdisj.
  set D1 := maxn (dconj psi) (dconj chi).
  set D2 := maxn (ddisj psi) (ddisj chi).
  have inner : forall j, (j < Wmax)%N ->
    (cdist (conjL (evalL chi s (t + j) :: [seq evalL psi s (t + i) | i <- iota 0 j]))
           (minS (rhoL chi s (t + j)) [seq rhoL psi s (t + i) | i <- iota 0 j])
     <= delta_conj + Bdef D1 D2)%R.
    move=> j hj.
    apply: one_step_conj.
    + exact: evalL_inrange.
    + by apply/allP => z /mapP[i hi ->]; exact: evalL_inrange.
    + by rewrite size_map size_iota.
    + apply: le_trans (IHc _ hWc) _; apply: Bdef_mono; [exact: leq_maxr | exact: leq_maxr].
    + apply: all2_map; apply/allP => i _.
      apply: le_trans (IHp _ hWp) _; apply: Bdef_mono; [exact: leq_maxl | exact: leq_maxl].
  rewrite BdefSconj.
  apply: one_step_disj.
  + apply: conjL_range; first exact: evalL_inrange.
    by apply/allP => z /mapP[i hi ->]; exact: evalL_inrange.
  + apply/allP => z /mapP[j hj ->]; apply: conjL_range; first exact: evalL_inrange.
    by apply/allP => w /mapP[i hi ->]; exact: evalL_inrange.
  + rewrite size_map size_iota; apply: leq_ltn_trans hWu; exact: leq_addl.
  + apply: inner; apply: leq_ltn_trans hWu; exact: leq_addr.
  + apply: all2_map; apply/allP => j hj; apply: inner.
    move: hj; rewrite mem_iota => /andP[_]; rewrite addSn ltnS => hjb.
    exact: leq_ltn_trans hjb hWu.
Qed.

(* ---------------------------------------------------------------------- *)
(* Theorem "Reuse", boolean part, separation form: if every point of the  *)
(* closed B-ball around the DL value lies strictly above theta, the        *)
(* formula is satisfied (dually below).  On real chains the premise is     *)
(* equivalent to  theta + B < evalL  (see ReuseInstances.v).               *)

Theorem reuse_boolean_sat phi s t :
  (maxwin phi <= Wmax)%N ->
  (forall y : L,
     (cdist (evalL phi s t) y <= Bdef (dconj phi) (ddisj phi))%R ->
     theta < y) ->
  sat nt_sat phi s t.
Proof.
move=> hW hsep; apply: (proj1 (rhoL_sound phi s t)).
by apply: hsep; exact: reuse_quantitative.
Qed.

Theorem reuse_boolean_unsat phi s t :
  (maxwin phi <= Wmax)%N ->
  (forall y : L,
     (cdist (evalL phi s t) y <= Bdef (dconj phi) (ddisj phi))%R ->
     y < theta) ->
  ~ sat nt_sat phi s t.
Proof.
move=> hW hsep; apply: (proj2 (rhoL_sound phi s t)).
by apply: hsep; exact: reuse_quantitative.
Qed.

End ReuseDefect.
