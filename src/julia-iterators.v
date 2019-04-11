Require Import SubtypeCorrectness.syntax.
Require Import SubtypeCorrectness.relations.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.EqdepFacts.

(* 
the important definitions are:
* normalize_subtype - subtyping through normalization
* subtype - subtyping through structural type iterators
* stack_subtype - subtyping through choice lists
*)


(* algorithmic normalization 
   computes the list of normalized clauses for a given type
*)
Fixpoint clauses(t:type): list type :=
  match t with
  | atom n => (atom n)::nil
  | tuple1 t1 => map tuple1 (clauses t1)
  | tuple2 t1 t2 => map (fun x => match x with (ti1, ti2) => tuple2 ti1 ti2 end)
                        (list_prod (clauses t1) (clauses t2))
  | union t1 t2 => (clauses t1) ++ (clauses t2)
  end.


(* Containment in the algorthmic normalization is equivalent to the InType proposition *)
Theorem clauses_in_type : forall t t', In t (clauses t') <-> InType t t'.
Proof.
  intros. generalize dependent t. induction t'.
  - cbn. intros. destruct t; try (split; intros; inject H; inject H0; fail).
    split; intros.
    + inject H; inject H0. constructor.
    + inject H. left. auto.
  - intros. cbn. split.
    + intros. rewrite in_map_iff in H. inject H. inject H0. apply IHt' in H1.
      constructor. auto.
    + intros. inject H. rewrite<- IHt' in H2. rewrite in_map_iff. exists ts.
      split; try auto.
  - intros. cbn. rewrite in_map_iff. split.
    + intros. inject H. destruct x. inject H0. rewrite in_prod_iff in H1. inject H1.
      rewrite IHt'1 in H. rewrite IHt'2 in H0. constructor; assumption.
    + intros. inject H. exists (ts1, ts2). split; auto.
      rewrite in_prod_iff. rewrite IHt'1. rewrite IHt'2. split; assumption.
  - intros. cbn. rewrite in_app_iff. rewrite IHt'1. rewrite IHt'2. split.
    + intros. inject H; [apply IUnionL|apply IUnionR]; assumption.
    + intros. inject H; [left|right]; assumption.
Qed.

(* Simple union-less subtyping, written in proof-generating style *)
Fixpoint base_subtype(t1 t2:type) : {BaseSubtype t1 t2} +
                                    {~(BaseSubtype t1 t2)}.
Proof.
  refine (match t1,t2 with
          | (atom i), (atom j) =>
            match (Nat.eq_dec i j) with
            | left a => left _
            | right a => right _ 
            end
          | (tuple1 ts1), (tuple1 ts2) =>
            match (base_subtype ts1 ts2) with
            | left a => _
            | right a => _ 
            end
          | (tuple2 ts1 ts1'), (tuple2 ts2 ts2') =>
            match (base_subtype ts1 ts2), (base_subtype ts1' ts2') with
            | left a, left b => _
            | right f, left b => _
            | left a, right f => _
            | right f, right b => _
            end
          | _, _ => _
          end); try (right; unfold not; intros; inject H; fail); try ( right; contradict f; inject f; auto; fail).
  - subst. constructor.
  - unfold not. intros. inject H. contradiction.
  - left. constructor. auto.
  - right. contradict a. inject a. auto.
  - left. constructor; assumption.
Defined.

(* we will proceed through three different subtyping algorithms each of which uses a different iteration
  strategy and prove that they all decide standard subtyping (denoted NormalSubtype). 

   We will begin with straightforward normalization. We proceed through two helper fixpoints that will
   decide inclusion between types and lists and lists and lists wrt base subtyping, then use them along
   with the algorithmic clauses function to decide subtyping using normalization. Note that these functions 
   require the evaluation of clauses, so nessecarily require exponential space to run *)

(* find a t' in ts such that t <: t'. Provide proof. *)
Fixpoint find_subtype(t:type)(ts:list type) : { t':type | In t' ts /\ BaseSubtype t t'} + {forall t', In t' ts -> ~ BaseSubtype t t'}.
Proof.
  destruct ts.
  - right. intros. inject H.
  - destruct (base_subtype t t0).
    + left. exists t0. split; [apply in_eq|assumption].
    + destruct (find_subtype t ts).
      * left. destruct s. exists x. destruct a. split; [apply in_cons; assumption| assumption].
      * right. intros. destruct H.
        ** subst. apply n.
        ** apply n0. apply H.
Defined.

(* show that for every t1 in ts1, there exists a t2 in ts2 such that t1 <: t2 with proof of completeness *)
Fixpoint th_subtype(ts1 ts2: list type) : {forall t1, In t1 ts1 -> exists t2, In t2 ts2 /\ BaseSubtype t1 t2} +
                                          {exists t1, In t1 ts1 /\ forall t2, In t2 ts2 -> ~BaseSubtype t1 t2}.
Proof.
  generalize dependent ts2. destruct ts1.
  - intros. left. intros. inject H.
  - intros. destruct (find_subtype t ts2).
    + destruct (th_subtype ts1 ts2).
      * left. intros. inject H.
        ** destruct s. exists x. apply a.
        ** apply e. apply H0.
      * right. inject e. exists x. inject H. split; try assumption.  apply in_cons. assumption.
    + right. exists t. split; [apply in_eq|]. apply n.
Defined.

(* subtyping via normalization *)
Definition normalize_subtype(t1 t2:type) : {NormalSubtype t1 t2} + { ~(NormalSubtype t1 t2)}.
Proof.
  destruct (th_subtype (clauses t1) (clauses t2)).
  - left. unfold NormalSubtype. intros. rewrite<- clauses_in_type in H. apply e in H. inject H.
    inject H0. rewrite clauses_in_type in H. exists x. split; assumption.
  - right. hnf. unfold NormalSubtype. intros. inject e. inject H0. rewrite clauses_in_type in H1. apply H in H1. inject H1. inject H0.
    rewrite<- clauses_in_type in H1.  apply H2 in H1. contradiction.
Defined.

(* with normalization out of the way, we can continue onto the meat of our contribution, the
   iterator-based subtyping algorithm. At a high level, the iterator-based algorithm "ticks"
   an iterator through each type, checking that there is a choice of the right iterator for
   every one of the left iterator's choice states. 

   To begin with, we will start by definining an iterator: *)

Inductive TypeIterator: type -> Set :=
| TIAtom : forall i, TypeIterator (atom i)
| TITuple1 : forall tp, TypeIterator tp -> TypeIterator (tuple1 tp)
| TITuple2 : forall t1 t2, TypeIterator t1 -> TypeIterator t2 -> TypeIterator (tuple2 t1 t2)
| TIUnionL : forall t1 t2, TypeIterator t1 -> TypeIterator (union t1 t2)
| TIUnionR : forall t1 t2, TypeIterator t2 -> TypeIterator (union t1 t2).


(* decides the iniital state for a type iterator over a given type *)
Fixpoint start_iterator (t:type):TypeIterator t :=
  match t with
  | (atom i) => TIAtom i
  | (tuple1 t) => TITuple1 t (start_iterator t)
  | (tuple2 t1 t2) => TITuple2 t1 t2 (start_iterator t1) (start_iterator t2)
  | (union t1 t2) => TIUnionL t1 t2 (start_iterator t1)
  end.

(* takes a state and then steps it to the next one, by flipping the final
   left choice to a right and padding the type out to length.  *)
Fixpoint next_state (t:type)(ti:TypeIterator t) : option (TypeIterator t) :=
  match ti with
  | TIAtom i => None
  | TITuple1 tip p => option_map (TITuple1 tip ) (next_state tip p)
  | TITuple2 ti1 ti2 p1 p2 =>
    match (next_state ti2 p2) with
    | Some (np2) => Some(TITuple2 ti1 ti2 p1 np2)
    | None =>
      match (next_state ti1 p1) with
      | Some (np1) => Some(TITuple2 ti1 ti2 np1 (start_iterator ti2))
      | None => None
      end
    end
  | TIUnionL ti1 ti2 pl =>
    match (next_state ti1 pl) with
    | Some(npl) => Some(TIUnionL ti1 ti2 npl)
    | None => Some(TIUnionR ti1 ti2 (start_iterator ti2))
    end
  | TIUnionR ti1 ti2 pr => option_map (TIUnionR ti1 ti2) (next_state ti2 pr)
  end.

(* produces the type at th ecurrent state of the iterator *)
Fixpoint current (t:type)(ti:TypeIterator t):type :=
  match ti with
  | TIAtom i => atom i
  | TITuple1 tip p => tuple1 (current tip p)
  | TITuple2 ti1 ti2 p1 p2 => tuple2 (current ti1 p1) (current ti2 p2)
  | TIUnionL ti1 ti2 pl => (current ti1 pl)
  | TIUnionR ti1 ti2 pr => (current ti2 pr)
  end.

(* counts the total number of steps an iterator will take over a given type *)
Fixpoint total_num (t:type):nat :=
  match t with
  | atom i => 1
  | tuple1 t => total_num t
  | tuple2 t1 t2 => (total_num t1) * (total_num t2)
  | union t1 t2 => (total_num t1) + (total_num t2)
  end.

(* counts the total number of steps the given iterator ti has remaining over 
   type t *)
Fixpoint iternum (t:type)(ti:TypeIterator t):nat :=
  match ti with
  | TIAtom i => 0
  | TITuple1 tip p => iternum tip p
  | TITuple2 ti1 ti2 p1 p2 =>
    (iternum ti1 p1) * (total_num ti2) + (iternum ti2 p2)
  | TIUnionL ti1 ti2 pl => (iternum ti1 pl) + (total_num ti2)
  | TIUnionR ti1 ti2 pr => (iternum ti2 pr)
  end.

(* some helper tactics. the use of dependent types in type iterator means that we end up 
   making equality arguments based on them a lot *)

Ltac open_exists :=
  match goal with [H : ex _ |- _ ] => destruct H  end.

Ltac eqdep_eq := 
    match goal with [H:existT ?A _ _ = existT ?A _ _ |- _] =>
                    apply Eqdep.EqdepTheory.inj_pair2 in H end; subst.

Definition type_tupler := (fun x : type * type => let (ti1, ti2) := x in tuple2 ti1 ti2).

(* the remaining relation relates type iterators to the list of types that remain to be
   stepped through. *)
Inductive Remaining  : forall t, TypeIterator t -> list type -> Prop :=
| TRemAtom : forall i, Remaining (atom i) (TIAtom i) ((atom i)::nil)
| TRemTuple1 : forall ti ii ls, Remaining ti ii ls -> Remaining (tuple1 ti) (TITuple1 ti ii) (map tuple1 ls)
| TRemTuple2 : forall ti1 ti2 ii1 ii2 hd ls1 ls2,
    Remaining ti1 ii1 (hd::ls1) -> Remaining ti2 ii2 ls2 -> Remaining (tuple2 ti1 ti2) (TITuple2 ti1 ti2 ii1 ii2) ((map (tuple2 hd) ls2) ++ (map type_tupler (list_prod ls1 (clauses ti2))))
| TRemUnionL : forall t1 t2 ii ls, Remaining t1 ii ls -> Remaining (union t1 t2) (TIUnionL t1 t2 ii) (ls ++ clauses t2)
| TRemUnionR : forall t1 t2 ii ls, Remaining t2 ii ls -> Remaining (union t1 t2) (TIUnionR t1 t2 ii) (ls).

(* simple helpers for option_map *)
Lemma option_map_spec1 : forall A B (e:B) (f:A->B) (x:option A), option_map f x = Some e -> exists v, x = Some v.
Proof.
  intros. destruct x.
  - cbn in *. inject H. exists a. auto.
  - cbn in H. inject H.
Qed.

Lemma option_map_spec2 : forall A B (f : A->B) (x:option A),option_map f x = None -> x = None.
Proof.
  intros. destruct x.
  - cbn in H. inject H.
  - auto.
Qed.

(* there is always at least one element remaining in the iterator, the element the iterator
   is "sitting" on *)
Lemma always_nonempty : forall t it l,
    Remaining t it l -> exists h, exists tl, l=h::tl.
Proof.
  intros. induction H; repeat open_exists; subst.
  - repeat eexists. 
  - rewrite map_cons. eexists; eauto. 
  - inject H2. rewrite map_cons. cbn. eexists. eauto.
  - cbn. eexists; eauto.
  - eexists; eauto.
Qed.

(* an initial iterator has the full set of normalized clauses remaining to be iterated *)
Lemma iterator_has_clauses :
  forall t, Remaining t (start_iterator t) (clauses t).
Proof.
  intros. induction t; cbn; try constructor.
  - apply IHt.
  - destruct (clauses t1).
    + exfalso. apply always_nonempty in IHt1. repeat open_exists.
      inversion H. 
    + cbn. rewrite map_app.
      replace (map (fun x : type * type => let (ti1, ti2) := x in tuple2 ti1 ti2)
                   (map (fun y : type => (t, y)) (clauses t2))) with (map (tuple2 t) (clauses t2)); revgoals.
      * rewrite map_map. apply map_ext_in. intros. auto. 
      * constructor; assumption.
  - assumption.
Qed.

(* if the next state is none, then the only remaining element is the one you're sitting on. *)
Lemma next_empty : forall t it ls, next_state t it = None -> Remaining t it ls -> exists l, ls = l :: nil.
Proof.
  intros. dependent induction it; cbn in H. 
  - exists (atom i). inject H0. auto. 
  - apply option_map_spec2 in H. inject H0. eqdep_eq. 
    eapply IHit in H; [|apply H3]. inject H. exists (tuple1 x). auto.
  - destruct (next_state t2 it2) eqn:Hn2; [inject H|]. destruct (next_state t1 it1) eqn:Hn1; [inject H | ].
    inject H0. repeat eqdep_eq.
    pose proof (IHit1 (hd :: ls1) eq_refl H6). pose proof (IHit2 ls2 eq_refl H7). inject H0. inject H1. inject H2.
    cbn. exists (tuple2 x x0). auto.
  - destruct (next_state t1 it); inject H.
  - apply option_map_spec2 in H. inject H0. eqdep_eq.
    eapply IHit in H; [|apply H5]. auto.
Qed.

(* if there is some non-empty list remaining and the next state exists, then it will have the
   tail of the original list remaining. you can see the induction principle coming? *)
Lemma next_step_next : forall t it it' h l,
    Remaining t it (h::l) -> next_state t it = Some it' ->
    Remaining t it' l.
Proof.
  intros. dependent induction it; intros; cbn in H0.
  - inject H0.
  - pose proof H0. apply option_map_spec1 in H0. open_exists.
    rewrite H0 in H1. cbn in H1. inject H1. 
    inject H. eqdep_eq. destruct ls; [cbn in H3; inject H3|]. cbn in H3.
    inject H3. constructor. eapply IHit; eauto.
  - destruct (next_state t2 it2) eqn:Hns2.
    + inject H0. inject H. repeat eqdep_eq. pose proof H6.
      apply always_nonempty in H6.
      repeat open_exists. subst. cbn in H5. inject H5. constructor; eauto.
    + destruct (next_state t1 it1) eqn:Hns; [|inject H0]. inject H0.
      inject H. repeat eqdep_eq. eapply next_empty in Hns2; eauto.
      open_exists. subst. cbn in H5. inject H5. eapply IHit1 in H3; eauto.
      pose proof H3. apply always_nonempty in H3. repeat open_exists. subst.
      replace (map type_tupler (list_prod (x0 :: x1) (clauses t2))) with
          ((map (tuple2 x0) (clauses t2)) ++ (map type_tupler (list_prod x1 (clauses t2)))); revgoals.
      * cbn. rewrite map_app. rewrite map_map. cbn. auto.
      * constructor; eauto. apply iterator_has_clauses.
  - destruct (next_state t1 it) eqn:Hns; inject H0; inject H; eqdep_eq;
      pose proof H1; apply always_nonempty in H1; repeat open_exists; subst;
        cbn in H4; inject H4; constructor.
    + eapply IHit; eauto.
    + apply next_empty in H; eauto. open_exists. inject H.
      apply iterator_has_clauses.
  - pose proof H0. apply option_map_spec1 in H0. open_exists.
    rewrite H0 in H1. cbn in H1. inject H1. constructor. inject H.
    eqdep_eq. eapply IHit; eauto. 
Qed.

(* every iterator has some remaining types *)
Lemma has_remaining : forall t it, exists l, Remaining t it l.
Proof.
  intros. dependent induction it; try (repeat open_exists; eexists; econstructor; fail).
  - repeat open_exists; eexists; econstructor; apply H.
  - repeat open_exists. pose proof H0. apply always_nonempty in H0.
    repeat open_exists. subst. eexists. econstructor; eauto.
  - repeat open_exists. eexists. econstructor. eauto.
  - repeat open_exists. eexists. econstructor. eauto.
Qed.

(* well... *)
Lemma length_clauses : forall t, total_num t = length (clauses t).
Proof.
  intros. induction t; cbn. 
  - auto.
  - rewrite map_length. auto.
  - rewrite map_length. rewrite prod_length. rewrite IHt1. rewrite IHt2. auto.
  - rewrite app_length. rewrite IHt1. rewrite IHt2. auto.
Qed.

(* the number of remaining choices to be made equals the number produced by iternum *)
Lemma length_remaining : forall t it l,
    Remaining t it l -> S(iternum t it) = length l.
Proof.
  intros. dependent induction it; inject H; repeat eqdep_eq.
  - cbn. auto.
  - cbn. rewrite map_length. erewrite IHit; eauto.
  - apply IHit1 in H5. apply IHit2 in H6. cbn.
    rewrite app_length. repeat rewrite map_length. rewrite prod_length.
    rewrite<- Nat.add_succ_r. rewrite H6. cbn in H5. inject H5.
    rewrite length_clauses. omega.
  - cbn. rewrite app_length. rewrite<- Nat.add_succ_l.
    erewrite IHit; eauto. rewrite length_clauses. auto.
  - cbn. erewrite IHit; eauto.
Qed.

(* there are monotonically fewer choices at each step of the iterator 
   this is the heart of the termination argument *)
Theorem iternum_monotonic : forall t (s s':TypeIterator t),
    Some(s') = next_state t s -> S(iternum t s') = iternum t s.
Proof.
  intros. pose proof (has_remaining _ s). symmetry in H. open_exists.
  pose proof H0. apply always_nonempty in H0. repeat open_exists. subst. 
  pose proof H1. eapply next_step_next in H1; eauto.
  apply length_remaining in H0. apply length_remaining in H1. cbn in H0.
  inject H0. congruence. 
Qed.

(* THe current function produces the first element off of the remaining list *)
Lemma current_state_head: forall t it a l, Remaining t it (a::l) ->
                                           a=(current t it).
Proof.
  intros. generalize dependent a. generalize dependent l. induction it.
  - intros. inject H. cbn. auto.
  - intros. cbn. inversion H. destruct ls; [cbn in H2;inject H2|].
    cbn in H2. inject H2. eqdep_eq. subst. apply IHit in H3. subst. auto.
  - intros. inject H. repeat eqdep_eq. cbn. apply IHit1 in H3. subst.
    pose proof H6. apply always_nonempty in H. repeat open_exists. subst. 
    apply IHit2 in H6. subst. cbn in H5. inject H5. auto.
  - intros. inject H. eqdep_eq. pose proof H1. apply always_nonempty in H.
    repeat open_exists. subst. apply IHit in H1. cbn. subst. cbn in H4.
    inject H4. auto.
  - intros. inject H. eqdep_eq. apply IHit in H4. subst. cbn. auto.
Qed.

(* if there's a next state we can't have 0 states remaining *)
Lemma cannot_be_end : forall t it it',
    next_state t it = Some it' -> iternum t it = 0 -> False.
Proof.
  intros. symmetry in H. apply iternum_monotonic in H.
  rewrite H0 in H. inject H.
Qed.

(* the meat of our proof. This provides an induction principle over
   types using type iterators. If you can prove your proposition for the 
   *final* state, the one for which there is no successor state and if the
   *following* state has it hold, then it can be said about the entire iterator.
   additionally, it gives us decidability for a bunch of future things *)
Fixpoint iter_recti (t : type) (P : TypeIterator t -> Set)
         (pi: forall it, next_state t it = None -> P it)
         (ps : forall it' it'', P it'' -> next_state t it' = Some it'' -> P it')
         (it : TypeIterator t) (n:nat)(Hn : n = iternum t it){struct n} : P it.
  refine (
  match next_state t it as nsp, n as n' return (next_state t it = nsp -> n = n' -> P it) with
  | Some it', S n'' => fun Heq Hneq => ps it it' (iter_recti t P pi ps it' n'' _) Heq
  | None, _ => fun Heq Hneq => pi it Heq
  | Some _, 0 => _
  end eq_refl eq_refl).
  - intros. contradict Hn. intro.
    eapply cannot_be_end; eauto. congruence.
  - abstract (symmetry in Heq; apply iternum_monotonic in Heq; subst;
    rewrite Hneq in Heq; apply eq_add_S in Heq; auto).
Defined.

(* a convienence wrapper around recti *)
Definition iter_rect
  (t:type) (P:TypeIterator t -> Set)
           (pi: forall it, next_state t it = None -> P it)
           (ps : forall it' it'', P it'' -> next_state t it' = Some it'' -> P it')
           (it : TypeIterator t) : P it :=
  iter_recti t P pi ps it (iternum t it) eq_refl. 

(* decide whether there exists a choice on the rhs for every choice 
   on the lhs, but using induction over type iterators to decide it *)
Definition exists_iter_inner(a b : type)(it:TypeIterator b) :
  ({ t | forall l, Remaining b it l -> In t l /\ BaseSubtype a t } +
   {forall t l, Remaining b it l -> In t l -> ~(BaseSubtype a t) }).
Proof.
  induction it using iter_rect. 
  - destruct (base_subtype a (current b it)).
    + left. exists (current b it). intros.
      eapply next_empty in H; eauto. inject H.
      apply current_state_head in H0. subst. split; eauto.
      apply in_eq. 
    + right. intros. eapply next_empty in H; eauto. inject H.
      inject H1; [|inject H].
      apply current_state_head in H0. subst. auto.
  - destruct (base_subtype a (current b it1)).
    + left. exists (current b it1). intros. split; auto.
      pose proof H0. apply always_nonempty in H1. repeat open_exists. subst.
      apply current_state_head in H0. rewrite H0. apply in_eq.
    + destruct IHit1.
      * left. destruct s. exists x. intros.
        pose proof H0. apply always_nonempty in H1. repeat open_exists.
        subst. eapply next_step_next in H0; eauto. apply a0 in H0.
        destruct H0. split; auto.
        apply in_cons. apply H0.
      * right. intros. pose proof H0. apply always_nonempty in H0.
        repeat open_exists. subst. inject H1.
        ** apply current_state_head in H2. subst. auto.
        ** eapply next_step_next in H; eauto.
Defined.

(* wrapper around exists_iter_inner *)
Definition exists_iter(a b : type) : 
  ({ t | InType t b /\ BaseSubtype a t } +
   {forall t, InType t b -> ~(BaseSubtype a t) }).
  destruct (exists_iter_inner a b (start_iterator b)).
  - left. destruct s. exists x. pose proof (a0 (clauses b) (iterator_has_clauses b)).
    rewrite<- clauses_in_type. auto.
  - right. intros. pose proof (n t (clauses b) (iterator_has_clauses b)).
    rewrite clauses_in_type in H0. apply H0 in H. auto.
Defined.

(* analogous to exists_iter_inner, but this time for the left hand side's forall 
   quantification. *)
Definition forall_iter_inner (a b : type) (it : TypeIterator a) :
  { forall l, Remaining a it l ->
              forall t, In t l ->
                        exists t', In t' (clauses b) /\ (BaseSubtype t t')} +
  { forall l, Remaining a it l ->
              exists t, In t l /\ forall t', In t' (clauses b) -> ~ (BaseSubtype t t')}.
Proof.
  induction it using iter_rect.
  - destruct (exists_iter (current a it) b).
    + left. intros. eapply next_empty in H; eauto. inject H. inject H1; [|inject H].
      destruct s. exists x. apply current_state_head in H0. subst.
      rewrite clauses_in_type. auto.
    + right. intros. eapply next_empty in H; eauto. inject H. exists x.
      split; [apply in_eq|]. intros. rewrite clauses_in_type in H. apply n in H.
      apply current_state_head in H0. subst. auto.
  - destruct (exists_iter (current a it1) b).
    + destruct IHit1.
      * left. intros. pose proof H0. apply always_nonempty in H2.
        repeat open_exists. subst.
        pose proof (current_state_head _ _ _ _ H0). 
        eapply next_step_next in H0; eauto. inject H1.
        ** destruct s. exists x. rewrite clauses_in_type. auto.
        ** eapply e in H0; eauto.
      * right. intros. pose proof H0. apply always_nonempty in H1.
        repeat open_exists. subst. eapply next_step_next in H0; eauto.
        apply e in H0. inject H0. exists x1. inject H1.
        split; try apply in_cons; auto.
    + right. intros. exists (current a it1).
      pose proof H0. apply always_nonempty in H1. repeat open_exists.
      subst. pose proof (current_state_head _ _ _ _ H0). subst.
      split; eauto.
      * apply in_eq.
      * intros. rewrite clauses_in_type in H1. apply n in H1. auto.
Defined.

(* and the convinence initial state *)
Definition forall_iter (a b : type) :
  { forall t, In t (clauses a) -> exists t', In t' (clauses b) /\ (BaseSubtype t t')} +
  { exists t, In t (clauses a) /\ forall t', In t' (clauses b) -> ~ (BaseSubtype t t')}.
Proof.
  destruct (forall_iter_inner a b (start_iterator a)).
  - left. pose proof (e _ (iterator_has_clauses a)). auto. 
  - right. pose proof (e _ (iterator_has_clauses a)). auto. 
Defined.

(* finally, we can decide subtyping soundly and completely using these helpers. Note that
the resultant theorem is identical despite the very different internals. *)
Definition subtype(a b:type) : {NormalSubtype a b} + {~NormalSubtype a b}.
  destruct (forall_iter a b).
  - left. unfold NormalSubtype. intros. rewrite<- clauses_in_type in H. apply e in H.
    inject H. exists x. rewrite clauses_in_type in H0. auto.
  - right. intro. unfold NormalSubtype in H. inject e. inject H0. rewrite clauses_in_type in H1.
    apply H in H1. inject H1. inject H0. eapply H2.
    + rewrite clauses_in_type. eauto.
    + auto.
Defined.

(* we have shown that the algorithm works with explicit iterators over types. However, 
we have yet to prove its operation when used with boolean stacks in place of the structural 
iterators. We now prove that we can decide subtyping using said boolean stacks. *)

(* our boolean stack representation *)
Definition st_context := list bool.

(* ValidPath sc t sc' means that sc is a valid path for t with some suffix sc', which is needed for 
   proper handling of tuples *)
Inductive ValidPath : st_context -> type -> st_context -> Prop :=
| VPLeft : forall r a b l,  ValidPath r a l-> ValidPath (false::r) (union a b) l
| VPRight : forall r a b l, ValidPath r b l -> ValidPath (true::r) (union a b) l
| VPAtom : forall r i, ValidPath r (atom i) r
| VPTuple1 : forall t r l, ValidPath r t l -> ValidPath r (tuple1 t) l
| VPTuple2 : forall t1 t2 r l1 l2, ValidPath r t1 l1 -> ValidPath l1 t2 l2 -> ValidPath r (tuple2 t1 t2) l2.

(* subset a type with a choice list *)
Fixpoint lookup_path(t:type)(p:st_context) : type * st_context :=
  match t, p with
  | atom i, _ => (t, p)
  | tuple1 t, _ => let (r,p) := lookup_path t p in (tuple1 r, p)
  | tuple2 t1 t2, _ =>
    let (r1,p1) := lookup_path t1 p in
    let (r2,p2) := lookup_path t2 p1 in
    (tuple2 r1 r2, p2)
  | union l r, false::rs => lookup_path l rs
  | union l r, true::rs => lookup_path r rs
  | _, nil => (t, nil)
  end.

(* if a path is valid, we can look up the type that it corresponds to *)
Lemma lookup_remains : forall t p r, ValidPath p t r -> exists t', lookup_path t p = (t',r).
Proof.
  intros. induction H.
  - inject IHValidPath. cbn. exists x. auto.
  - inject IHValidPath. cbn. eexists; eauto.
  - exists (atom i). auto.
  - cbn. inject IHValidPath. rewrite H0. eexists; eauto.
  - cbn. inject IHValidPath1. inject IHValidPath2. rewrite H1. rewrite H2. eexists; eauto.
Qed.

(* if a path is valid and has some suffix r, then we can add some additional suffix p' onto it to give a resultant suffix r ++ p' *)
Lemma lookup_left : forall t t' r p p', ValidPath p t r -> forall Hlp : lookup_path t p = (t',r), lookup_path t (p++p') = (t',r++p').
Proof.
  intros. generalize dependent p. generalize dependent p'. generalize dependent t'. generalize dependent r. induction t;intros.
  - cbn in *. inject Hlp. auto.
  - cbn in *. destruct (lookup_path t p) eqn:Hlp1. inject Hlp. eapply IHt in Hlp1.
    + rewrite Hlp1. auto.
    + inject H. auto.
  - cbn in *. inject H.
    destruct (lookup_remains t1 p l1); eauto. destruct (lookup_remains t2 l1 r); eauto.
    rewrite H in Hlp. rewrite H0 in Hlp. inject Hlp.
    erewrite IHt1; eauto. erewrite IHt2; eauto.
  - cbn. destruct p.
    + inject H.
    + destruct b; cbn in *; inject H; [apply IHt2|apply IHt1]; eauto.
Qed.

(* same as lookup_left but for ValidPath directly *)
Lemma valid_extend : forall t p r p', ValidPath p t r -> ValidPath (p ++ p') t (r ++ p').
Proof.
  intros. induction H; cbn; try (constructor; eauto; fail).
  - econstructor.
    + apply IHValidPath1.
    + apply IHValidPath2.
Qed.

(* takes a typeiterator and makes it into a path *)
Fixpoint iterator_to_path(t:type)(it:TypeIterator t):st_context :=
   match it with
   | TIAtom _ => nil
   | TITuple1 tp it1 => iterator_to_path tp it1
   | TITuple2 t1 t2 it1 it2 => (iterator_to_path t1 it1) ++ (iterator_to_path t2 it2)
   | TIUnionL t1 _ it1 => false :: (iterator_to_path t1 it1)
   | TIUnionR _ t2 it1 => true :: (iterator_to_path t2 it1)
   end.

(* all type iterators will be translated into suffix-free paths for the types that they iterate over *)
Lemma itp_valid : forall t it, ValidPath (iterator_to_path t it) t nil.
Proof.
  intros. induction it; cbn in *; try (econstructor; eauto; fail).
  econstructor.
  - apply valid_extend. eauto.
  - cbn. eauto.
Qed.

(* the result of looking up the converted path from an iterator is the current state *)
Lemma itp_correct : forall t it, current t it = fst (lookup_path t (iterator_to_path t it)).
Proof.
  intros. induction it.
  - cbn. auto.
  - cbn in *. destruct (lookup_path tp (iterator_to_path tp it)). cbn in *. subst. auto.
  - cbn in *. destruct (lookup_path t1 (iterator_to_path t1 it1)) eqn:itp1. erewrite lookup_left with (r:= nil).
    + cbn.  destruct (lookup_path t2 (iterator_to_path t2 it2)). cbn in *. subst. eauto.
    + apply itp_valid.
    + rewrite IHit1. cbn in *. subst. pose proof (itp_valid t1 it1).
      apply lookup_remains in H. inject H. rewrite H0 in itp1. inject itp1.
      auto.
  - cbn in *. eauto.
  - cbn in *. eauto.
Qed.

(* see the paper for details; identifies the last left choice in the list, makes it a right, and chops the rest off *)
Fixpoint flip_last_left(ls:st_context):=
  match ls with
  | false::rs =>
    match flip_last_left rs with
    | Some s => Some(false :: s)
    | None => Some(true::nil)
    end
  | true::rs =>
    match flip_last_left rs with
    | Some s => Some(true::s)
    | None => None
    end
  | nil => None
  end.

(* after getting chopped off by flip_last_left, extend_list fixes the end of the list up with
   lefts until it reaches leaves. also used to produce the inital state when called with an empty initial list *)
Fixpoint extend_list(t:type)(ls:st_context) :=
  match t,ls with
  | atom i, _ => (nil, ls)
  | tuple1 t, _ => extend_list t ls
  | tuple2 t1 t2, _ =>
    let (hd1,tl1) := extend_list t1 ls in
    let (hd2,tl2) := extend_list t2 tl1 in
    (hd1 ++ hd2, tl2)
  | union l r, false::rs => extend_list l rs
  | union l r, true::rs => extend_list r rs
  | union l r, nil =>
    let (hd,tl) := extend_list l nil in (false :: hd, tl)
  end.

(* helpers *)
Lemma option_map_spec1' : forall (A B : Type) (e : B) (f : A -> B) (x : option A),
    option_map f x = Some e -> exists v : A, f v = e /\ x = Some v.
Proof.
  intros. destruct x.
  - cbn in H. inject H. exists a; eauto.
  - cbn in H. inject H.
Qed.

(* every element in a new choice list is false *)
Lemma new_it_false : forall t l, In l (iterator_to_path t (start_iterator t)) -> l = false.
Proof.
  intros. induction t; cbn in *. 
  - inject H.
  - apply IHt in H. auto.
  - apply in_app_or in H. inject H; [apply IHt1 in H0|apply IHt2 in H0]; auto.
  - inject H; [ symmetry | apply IHt1 ]; auto.
Qed.

(* in a choice list that is finished, every element must be true *)
Lemma old_it_true :
  forall t it, next_state t it = None ->
               forall el, In el (iterator_to_path t it) -> el = true.
Proof.
  intros. induction it; cbn in *.
  - inject H0.
  - apply option_map_spec2 in H. apply IHit in H; auto.
  - destruct (next_state t2 it2); destruct (next_state t1 it1); try inject H.
    apply in_app_or in H0. destruct H0; [apply IHit1|apply IHit2]; auto. 
  - destruct (next_state t1 it); inject H.
  - apply option_map_spec2 in H. destruct H0; [symmetry|];auto.
Qed.

(* we can break down a choice list as follows:
   if ls steps to ls', then the following must be true:
   ls must consist of some head, followed by a false (a left choice), followed 
      by some tail that consists solely of trues (right choices). we will flip this choice
   ls' must consist of that same head, followed by a true (a right choice) in place of the old false, 
      with the new tail consisting of falses (left choices). *)
Lemma ns_breakdown : forall t it it' ls ls',
    next_state t it = Some it' ->
    iterator_to_path t it = ls ->
    iterator_to_path t it' = ls' ->
    exists hd tl tl',
      ls = hd ++ (false::tl) /\
      ls' = hd ++ (true :: tl') /\
      (forall el, In el tl' -> el = false) /\
      (forall el, In el tl -> el = true).
Proof.
  intros. generalize dependent it'. generalize dependent ls. generalize dependent ls'.
  dependent induction it.
  - intros. cbn in *. inject H.
  - intros. cbn in *. apply option_map_spec1' in H. destruct H as [it'' [H2 H3]].
    rewrite<- H2 in H1. cbn in H1. edestruct IHit as [hd' [tl'' [tl''' H4]]];
                                     try eassumption.
    subst. eexists. eexists. eexists. apply H4.
  - intros. cbn in *. destruct (next_state t2 it2) eqn:Hit2.
    + inject H. cbn. edestruct IHit2 as [hd' [tl'' [tl''' [H1 [H2 [H3 H4]]]]]];
                       [ apply eq_refl | apply eq_refl | apply eq_refl | ].
      exists (iterator_to_path t1 it1 ++ hd'). exists tl''. exists tl'''.
      rewrite H1. rewrite H2. repeat rewrite app_assoc. auto.
    + clear IHit2. destruct (next_state t1 it1).
      * inject H. cbn. edestruct IHit1 as [hd' [tl'' [tl''' [H1 [H2 [H3 H4]]]]]];
                         [apply eq_refl | apply eq_refl | apply eq_refl |].
        rewrite H1. rewrite H2. rewrite<- app_assoc. rewrite<- app_assoc. 
        exists hd'. exists (tl'' ++ iterator_to_path t2 it2).
        exists (tl''' ++ iterator_to_path t2 (start_iterator t2)). cbn. repeat split; auto.
        ** intros. apply in_app_or in H. inject H.
           *** apply H3. auto.
           *** apply new_it_false in H0. auto.
        ** intros. apply in_app_or in H. destruct H; auto. eapply old_it_true in H; auto.
      * inject H.
  - intros. cbn in *. destruct (next_state t1 it) eqn:Hit1.
    + inject H. cbn. edestruct IHit as [hd' [tl'' [tl''' [H1 [H2 [H3 H4]]]]]];
                       [ apply eq_refl | apply eq_refl | apply eq_refl | ].
      rewrite H1. rewrite H2. exists (false::hd'). exists tl''. exists tl'''.
      cbn; split; auto.
    + inject H. cbn. exists nil. cbn. exists (iterator_to_path t1 it).
      exists (iterator_to_path t2 (start_iterator t2)). repeat split; auto.
      * intros. eapply new_it_false. apply H.
      * intros. apply old_it_true in H; auto.
  - intros. cbn in *. apply option_map_spec1' in H. inject H. destruct H2.
    subst. cbn. edestruct IHit as [hd' [tl'' [tl''' [H1 [H2 [H3 H4]]]]]];
                  [ apply eq_refl | apply H0 | apply eq_refl | ].
    rewrite H1. rewrite H2. exists (true :: hd'). repeat eexists. auto.
    apply H4. 
Qed.

(* if every element is true (e.g. right), then there is no more state to go *)
Lemma flip_last_left_emp : forall tl,
    (forall el, In el tl -> el = true) ->
    flip_last_left tl = None.
Proof.
  intros. induction tl.
  - auto.
  - cbn. pose proof (H a (in_eq _ _)). subst. rewrite IHtl; auto.
    intros. apply H. apply in_cons; auto. 
Qed.

(* kinda the same as ns_breakdown, just for flip_last_left alone and without the suffix *)
Lemma flip_last_left_corr : forall hd tl,
    (forall el, In el tl -> el = true) -> 
    flip_last_left (hd ++ (false :: tl)) = Some (hd ++ true :: nil).
Proof. 
  intros. generalize dependent tl. induction hd.
  - intros. cbn in *. apply flip_last_left_emp in H. rewrite H. auto.
  - intros. cbn in *. rewrite IHhd; auto. destruct a; auto. 
Qed.

(* helper for app *)
Lemma split_app : forall tl a b hd,
    (forall el, In el tl -> el = false) ->
    a ++ b = hd ++ true:: tl ->
      (exists tl', a = hd ++ true :: tl' /\ tl = tl' ++ b) \/
      (exists hd', b = hd' ++ true :: tl /\ hd = a ++ hd').
Proof.
  intros. generalize dependent tl. generalize dependent a. generalize dependent b. induction hd; intros.
  - cbn in H0. destruct a.
    + cbn in H0. subst. right. exists nil. cbn. auto.
    + cbn in H0. inject H0. left. exists a. cbn. auto.
  - cbn in *. destruct a0.
    + cbn in H0. subst. right. exists (a::hd); split; eauto.
    + cbn in H0. inject H0.
      * apply IHhd in H3; auto. destruct H3.
        ** destruct H0 as [tl' [H0 H1]]. subst. cbn. left. exists tl'. split; auto.
        ** destruct H0 as [hd' [H0 H1]]. subst. cbn. right. exists hd'. split; auto.
Qed.

(* starting an iterator and converting it to a list is equivalent to extending the empty list to a type *)
Lemma extend_start : forall t, extend_list t nil = (iterator_to_path t (start_iterator t), nil).
Proof.
  intros. induction t; cbn in *; auto.
  - rewrite IHt1. rewrite IHt2. auto.
  - rewrite IHt1. auto.
Qed.

(* if every element in a path from an iterator is false, then it must be the initial iterator *)
Lemma false_empty_it : forall t it, (forall el, In el (iterator_to_path t it) -> el = false) -> it = start_iterator t.
Proof.
  intros. dependent induction it; cbn in *; auto.
  - apply IHit in H. subst. auto.
  - rewrite IHit1; [ rewrite IHit2; auto | ]; intros; apply H; apply in_or_app; [right|left]; auto.
  - rewrite IHit; auto.
  - assert (true = false).
    + apply H. left. auto.
    + inject H0.
Qed.

(* extend_list will indeed pad the given list out to the correct length for the type *)
Lemma extends_corr : forall t it,
  (forall hd tl,
      (forall el, In el tl -> el = false) -> 
      iterator_to_path t it = hd ++ true :: tl ->
      extend_list t (hd ++ true::nil) = (tl, nil)) /\
  (forall tl, extend_list t ((iterator_to_path t it) ++ tl) = (nil, tl)).
Proof.
  intros. dependent induction it; intros. 
  - cbn in *. split; intros; auto. symmetry in H0. apply app_eq_nil in H0. destruct H0. inject H1.
  - cbn in *. destruct IHit. split; intros.
    + intros. eapply H in H1; eauto.
    + apply H0.
  - cbn in *. split. 
    + intros. apply split_app in H0; auto. destruct H0 as [[tl' [H1 H2]]|[hd' [H1 H2]]]; subst; cbn in *.
      * apply IHit1 in H1. 
        ** rewrite H1. assert (it2 = start_iterator t2).
           { apply false_empty_it. intros. apply H. apply in_or_app. auto. }
           rewrite H0. rewrite extend_start. auto.
        ** intros. apply H. apply in_or_app. auto.
      * destruct IHit1. rewrite<- app_assoc. rewrite H2. apply IHit2 in H1.
        ** rewrite H1. cbn. auto.
        ** auto.
    + intros. destruct IHit1. rewrite<- app_assoc. rewrite H0. destruct IHit2. rewrite H2. auto.
  - cbn in *. split.
    + intros. destruct hd; [cbn in H0; inject H0|].
      cbn in H0. inject H0. apply IHit; auto.
    + intros. apply IHit.
  - split; intros.
    + cbn in H0. cbn. destruct hd.
      * cbn in H0. inject H0. cbn. apply false_empty_it in H. subst.
        rewrite extend_start. auto.
      * cbn in *. inject H0. apply IHit in H3; auto.
    + cbn in *. apply IHit.
Qed.

(* steps a context forward to the next state, using both extend_list and flip_last_left *)
Definition step_ctx (t : type) (pth:st_context) : option st_context := option_map (fun x => x ++ (fst (extend_list t x))) (flip_last_left pth).

(* step_ctx is equivalent to next_state under iterator_to_path conversion *)
Lemma list_step_correct_ex : forall t it it',
    next_state t it = Some it' ->
    step_ctx t (iterator_to_path t it) = Some (iterator_to_path t it').
Proof.
  intros. eapply ns_breakdown in H; [| apply eq_refl | apply eq_refl]. destruct H as [hd [tl [tl' [H [H0 [H1 H2]]]]]].
  rewrite H. rewrite H0. pose proof (flip_last_left_corr hd tl H2). unfold step_ctx. rewrite flip_last_left_corr; auto. cbn.
  pose proof (extends_corr t it'). destruct H4. clear H5. apply H4 in H0; auto. rewrite H0. cbn. rewrite<- app_assoc. cbn.
  auto.
Qed.

(* still equvialent even at the end of the iterator *)
Lemma list_step_correct_nex : forall t it,
    next_state t it = None ->
    option_map (fun x => x ++ (fst (extend_list t x))) (flip_last_left (iterator_to_path t it)) = None.
Proof.
  intros. rewrite flip_last_left_emp.
  - auto.
  - apply old_it_true; auto.
Qed.

(* identical for all iterator states, agglomeration of the previous two *)
Lemma list_step_correct : forall t it,
    step_ctx t (iterator_to_path t it) =
    (option_map (iterator_to_path t) (next_state t it)).
Proof.
  intros. destruct (next_state t it) eqn:Hns.
  - apply list_step_correct_ex in Hns. cbn. auto.
  - apply list_step_correct_nex in Hns. cbn. auto.
Qed.

Ltac hyp_bs :=
         match goal with [H: (if (base_subtype ?a ?b) then _ else _) = _ |- _ ] => destruct (base_subtype a b) end.
Ltac goal_bs :=
  match goal with [ |- (if (base_subtype ?a ?b) then _ else _) = _ ] => destruct (base_subtype a b) end.

(* we can go from propositional BaseSubtype to base_subtype trivially *)
Lemma bs_alg : forall a b, BaseSubtype a b -> exists p, base_subtype a b = left p.
Proof.
  intros. destruct (base_subtype a b).
  - eexists; eauto.
  - apply n in H. inversion H.
Qed.

(* exists subtyping! Iterates through the type b using the choice list cex checking
   using base_subtype if the result is a supertype of a *)
Fixpoint ex_subtype (a b : type)(cex :st_context)(fuel:nat) : option bool :=
  match base_subtype a (fst (lookup_path b cex)) with
  | left _ => Some true
  | right _ =>
    match step_ctx b cex with
    | Some ns =>
      match fuel with
      | S n => ex_subtype a b ns n
      | 0 => None
      end
    | None => Some false
    end
  end.

(* there exists some amount of fuel for which ex_subtype will terminate with a concrete result *)
Lemma ex_sub_len : forall a b, { r | exists n, ex_subtype a b (fst (extend_list b nil)) n = Some r}.
Proof.
  intros. remember (fst (extend_list b nil)). rewrite extend_start in Heql. cbn in *. remember (start_iterator b). clear Heqt.
  subst. induction t using iter_rect.
  - destruct (base_subtype a (fst (lookup_path b (iterator_to_path b t)))).
    + exists true. exists 0. cbn.  apply bs_alg in b0. destruct b0. rewrite H0. auto.
    + exists false. exists 0. cbn. goal_bs; auto.
      * contradict n; auto.
      * rewrite list_step_correct. rewrite H. cbn. auto. 
  - destruct IHt1. destruct x.
    + exists true. destruct e. exists (S x). cbn. goal_bs; auto. rewrite list_step_correct. rewrite H. cbn. auto.
    + destruct (base_subtype a (fst (lookup_path b (iterator_to_path b t1)))).
      * exists true. exists 0. cbn. apply bs_alg in b0. destruct b0. rewrite H0. auto.
      * exists false. destruct e. exists (S x). cbn. goal_bs.
        **  contradict n; auto.
        ** rewrite list_step_correct. rewrite H. cbn. auto.
Qed.

(* wrapper for the latter *)
Definition ex_sub_ex : forall (a b : type), bool.
Proof.
  intros. destruct (ex_sub_len a b). apply x.
Defined.

(* forall-exists subtyping, which iterates through a using cfa checking using ex_sub_ex if a under cfa is a subtype 
   of some instantiation of b *)
Fixpoint fa_ex_subtype (a b : type)(cfa : st_context)(fuel:nat) : option bool :=
  match ex_sub_ex (fst (lookup_path a cfa)) b with
  | true =>
    match step_ctx a cfa with
    | Some ns =>
      match fuel with
      | S n =>fa_ex_subtype a b ns n
      | 0 => None
      end
    | None => Some true
    end
  | _ => Some false
  end.

(* there is only a single remaining list for any given type and type iterator *)
Lemma remaining_uniq : forall t it l l', Remaining t it l -> Remaining t it l' -> l = l'.
Proof.
  intros. generalize dependent l. generalize dependent l'.
  dependent induction it; intros; inject H0; inject H; repeat eqdep_eq.
  - auto. 
  - rewrite (IHit _ H3 _ H4). auto.
  - pose proof (IHit1 _ H6 _ H9). pose proof (IHit2 _ H7 _ H10). subst. rewrite H in *.
    inject H. auto.
  - rewrite (IHit _ H5 _ H6). auto.
  - rewrite (IHit _ H5 _ H6). auto.
Qed.

Lemma app_cons_split : forall T a (b:list T), a :: b = (a::nil) ++ b.
Proof.
  intros. cbn; auto.
Qed.

(* if there is some following state and that state has l remaining elements, then  
   the current state has remaining elements of the current element appended onto the l elements *)
Lemma remaining_fwd: forall t c1 c2 l, next_state t c1 = Some c2 -> Remaining t c2 l -> Remaining t c1 (current t c1::l).
Proof.
  intros. generalize dependent c2. generalize dependent l. induction c1; intros; cbn in *.
  - inject H.
  - apply option_map_spec1' in H. destruct H as [c2' [H H1]]. subst. inject H0. eqdep_eq. rewrite<- map_cons. constructor. eapply IHc1; eauto.
  - destruct (next_state t2 c1_2) eqn:Hns2.
    + inject H. inject H0. repeat eqdep_eq. rewrite app_comm_cons. rewrite current_state_head with (t:=t1)(it:=c1_1)(a:=hd)(l:= ls1); auto. rewrite<- map_cons. constructor.
      * pose proof (current_state_head _ _ _ _ H5). rewrite<- H. auto.
      * eapply IHc1_2; eauto.
    + destruct (next_state t1 c1_1) eqn:Hns1.
      * inject H. inject H0. repeat eqdep_eq.
        pose proof (IHc1_1 _ t eq_refl H5).
        pose proof (iterator_has_clauses t2).
        pose proof (remaining_uniq _ _ _ _ H6 H0). subst.
        pose proof (map_app type_tupler
                            (list_prod (hd::nil) (clauses t2))
                            (list_prod ls1 (clauses t2))).
        cbn in H1. repeat rewrite app_nil_r in H1.
        assert (map type_tupler (map (fun y : type => (hd, y)) (clauses t2)) =
                map (tuple2 hd) (clauses t2)).
        { clear. induction (clauses t2); cbn in *; auto. rewrite<- IHl. auto. }
        rewrite H2 in H1. clear H2. rewrite<- H1. clear H1. 
        assert (map (fun y : type => (hd, y)) (clauses t2) ++ list_prod ls1 (clauses t2) =
                list_prod (hd::ls1) (clauses t2)); auto.
        rewrite H1. clear H1. rewrite app_cons_split.
        assert ((tuple2 (current t1 c1_1) (current t2 c1_2))::nil =
                map (tuple2 (current t1 c1_1)) ((current t2 c1_2)::nil)); auto.
        rewrite H1. clear H1.
        constructor; auto. destruct (has_remaining t2 c1_2). 
        eapply next_empty in Hns2; eauto. destruct Hns2. subst.
        rewrite<- (current_state_head _ _ _ _ H1). auto.
      * inject H.
  - destruct (next_state t1 c1) eqn:Hns; inject H; inject H0; eqdep_eq.  
    + apply IHc1 in H4; auto; try eqdep_eq.
      rewrite app_comm_cons. constructor. auto.
    + rewrite app_cons_split. pose proof (iterator_has_clauses t2).
      pose proof (remaining_uniq _ _ _ _ H4 H). subst. 
      apply TRemUnionL. destruct (has_remaining _ c1). eapply next_empty in Hns; eauto.
      destruct Hns. subst. rewrite (current_state_head _ _ _ _ H0) in H0. auto.
  - apply option_map_spec1' in H. destruct H. destruct H. subst. constructor.
    inject H0. eqdep_eq. eapply IHc1; eauto.
Qed.

(* there is always some current element for literally every type iterator *)
Lemma nonempty_rem : forall t it, exists tl, Remaining t it ((current t it)::tl).
Proof.
  intros.
  destruct (has_remaining _ it).
  destruct (always_nonempty _ _ _ H) as [hd [tl H0]]. subst.
  pose proof (current_state_head _ _ _ _ H). subst. 
  repeat eexists. apply H.
Qed.

(* ex_subtype will produce true iff exists_iter_inner (the one with the explicit structural iterator)
   produces true *)
Lemma ex_sub_corr_eq : forall a b it,
    (exists pf, exists_iter_inner a b it = inleft pf) <->
               exists n, ex_subtype a b (iterator_to_path b it) n = Some true.
Proof.
  intros; split. 
  - intros. induction it using iter_rect.
    + destruct H. destruct x. clear H. destruct (has_remaining _ it).
      destruct (next_empty _ _ _ H0 H). subst. pose proof (a0 _ H).
      destruct H1. inject H1; [|inject H3]. exists 0. cbn. apply bs_alg in H2.
      destruct H2. apply current_state_head in H. subst.
      rewrite<- itp_correct. rewrite H1. auto.
    + destruct H. destruct x. clear H.
      destruct (nonempty_rem _ it1) as [tl H1].
      pose proof (next_step_next _ _ _ _ _ H1 H0).
      apply a0 in H1. destruct H1.  inject H1.
      * exists 0. cbn. apply bs_alg in H2. destruct H2.
        rewrite<- itp_correct. rewrite H1. auto.    
      * destruct IHit1.
        ** pose proof (remaining_fwd _ _ _ _ H0 H). apply a0 in H1.
           destruct H1. 
           destruct (exists_iter_inner a b it2).
           *** exists s. auto. 
           *** exfalso. specialize (n x tl).
               apply n in H2; eauto.
        ** exists (S x0). cbn. goal_bs; auto. rewrite list_step_correct.
           rewrite H0. cbn. auto.
  - intros. induction it using iter_rect.
    + destruct H as [fuel Haex]. destruct fuel.
      * cbn in Haex. hyp_bs.
        ** destruct (exists_iter_inner a b it).
           *** exists s. auto.
           *** destruct (nonempty_rem _ it) as [tl H1].
               destruct (next_empty _ _ _ H0 H1). inject H.
               eapply n in H1; [|apply in_eq].
               rewrite<- itp_correct in b0. contradict b0. apply H1.
        ** destruct (step_ctx b (iterator_to_path b it)); inject Haex.
      * destruct (exists_iter_inner a b it).
        ** exists s. auto.
        ** destruct (nonempty_rem _ it) as [tl H1]. destruct (next_empty _ _ _ H0 H1). inject H.
           cbn in Haex. rewrite<- itp_correct in Haex. rewrite list_step_correct in Haex.
           rewrite H0 in Haex. cbn in Haex.
           eapply n in H1; [|apply in_eq]. contradict Haex.
           destruct (base_subtype a (current b it)).
           *** contradict b0. apply H1.
           *** unfold not. intros. inject H.
    + destruct H. destruct x; cbn in *; hyp_bs; try (rewrite<- itp_correct in b0).
      * destruct (exists_iter_inner a b it1).
        ** exists s. auto.
        ** destruct (nonempty_rem _ it1). eapply n in H1; [|apply in_eq]. contradict b0. auto.
      * destruct (step_ctx b (iterator_to_path b it1)); inject H.
      * destruct (exists_iter_inner a b it1); [exists s; eauto|].
        destruct (nonempty_rem _ it1). eapply n in H1; [|apply in_eq]. contradict b0. auto.
      * destruct (step_ctx b (iterator_to_path b it1)) eqn:Hns; try inject H.
        rewrite list_step_correct in Hns. destruct IHit1.
        ** exists x. rewrite H0 in Hns. cbn in Hns. inject Hns. auto.
        ** destruct x0. clear H1. destruct (exists_iter_inner a b it1); [eexists; auto|].
           destruct (nonempty_rem _ it1). pose proof (next_step_next _ _ _ _ _ H1 H0).
           apply a0 in H2. destruct H2. 
           eapply n0 in H1; [|apply in_cons; eauto]. contradict H1. auto.
Qed.

(* if exists subtyping is not true, then it must be false. No midde ground here *)
Lemma ex_sub_always_ne : forall a b it, (exists n, ex_subtype a b (iterator_to_path b it) n = Some false) <->
                                        forall m, ex_subtype a b (iterator_to_path b it) m <> Some true.
Proof.
  intros. split; intros.
  - generalize dependent m. induction it using iter_rect.
    + intros. destruct H.
      destruct x; cbn in H; hyp_bs; try (inject H; fail); rewrite list_step_correct in H; rewrite H0 in H; cbn in H;
        destruct m; cbn; destruct (base_subtype a (fst (lookup_path b (iterator_to_path b it))));
          try (contradict n; apply b0; fail);
          try (destruct (step_ctx b (iterator_to_path b it)); intro; inject H1; fail);
          rewrite list_step_correct; rewrite H0; cbn; intro; inject H1.
    + destruct H as [n He]. intros. destruct m.
      * cbn. destruct n; cbn in *; hyp_bs; try (inject He; fail); rewrite list_step_correct in *;
               rewrite H0 in *; cbn in *; intro; inject H.
      * cbn; destruct n; cbn in *; rewrite list_step_correct in *; rewrite H0 in *; cbn in *; hyp_bs; try (inject He).
        apply IHit1. exists n. auto.
  - induction it using iter_rect.
    + specialize (H 0). exists 0. cbn in *. destruct (base_subtype a (fst (lookup_path b (iterator_to_path b it)))).
      * exfalso. apply H. auto.
      * rewrite list_step_correct in *. rewrite H0 in *. cbn in *. auto.
    + destruct IHit1.
      * intros. specialize (H (S m)). cbn in H. destruct (base_subtype a (fst (lookup_path b (iterator_to_path b it1)))).
        ** contradict H. auto.
        ** rewrite list_step_correct in H. rewrite H0 in H. cbn in *. apply H.
      * exists (S x). specialize (H (S x)). cbn in *. destruct (base_subtype a (fst (lookup_path b (iterator_to_path b it1)))).
        ** contradict H. auto.
        ** rewrite list_step_correct in *. rewrite H0 in *. cbn in *. apply H1.     
Qed.

(* helper *)
Lemma neg_exists_is_forall : (forall t (P : t -> Prop), ~(exists x, P x) <-> forall x, ~ (P x)).
Proof.
  repeat intro. split.
    - repeat intro. apply H. exists x. auto.
    - repeat intro. destruct H0. contradict H0. apply H.
Qed.

(* if exists_iter_inner thinks that a b are not subtypes, then so will ex_subtype. Shown by negating
   both sides of the iff in  ex_sub_corr_eq and using ex_sub_always_ne to get rid of the out-of-fuel cases *)
Lemma ex_sub_corr_ieq : forall a b it,
    (exists pf, exists_iter_inner a b it = inright pf) <->
    (exists n, ex_subtype a b (iterator_to_path b it) n = Some false).
Proof.
  intros. pose proof (ex_sub_corr_eq a b it). apply not_iff_compat in H.
  repeat rewrite neg_exists_is_forall in H. split.
  - intros. destruct H0. rewrite<- ex_sub_always_ne in H. apply H. intros. rewrite H0. intro. inject H1.
  - intros. rewrite<- ex_sub_always_ne in H. rewrite<- H in H0. destruct (exists_iter_inner a b it).
    + pose proof (H0 s). exfalso. apply H1. auto.
    + exists n. auto.
Qed.

(* like  ex_sub_corr_eq but for forall-exists this time *)
Lemma fa_sub_corr_eq: forall a b it,
    (exists pf, forall_iter_inner a b it = left pf) <->
    exists n, fa_ex_subtype a b (iterator_to_path a it) n = Some true.
Proof.
  intros. split; intros.
  - induction it using iter_rect.
    + destruct H. destruct (nonempty_rem _ it) as [tl Hrm]. eapply x in Hrm; [|apply in_eq].
      destruct Hrm as [t [Hin Hbs]]. exists 1. cbn. rewrite<- itp_correct. unfold ex_sub_ex. destruct (ex_sub_len _ _).
      destruct e. destruct x0.
      * rewrite list_step_correct. rewrite H0. cbn. auto.
      * assert (exists n, ex_subtype (current a it) b (fst (extend_list b nil)) n = Some false).
        { exists x1. auto. } rewrite extend_start in H2. cbn in H2.
        rewrite<- ex_sub_corr_ieq in H2. destruct H2. clear H2.
        specialize (x0 t (clauses b) (iterator_has_clauses _) Hin). contradict x0. auto.
    + destruct H. destruct (nonempty_rem _ it1). pose proof (next_step_next _ _ _ _ _ H1 H0). destruct IHit1.
      * destruct (forall_iter_inner a b it2).
        ** eexists; eauto.
        ** apply e in H2. destruct H2. destruct H2. eapply x in H1; [|apply in_cons; apply H2]. destruct H1 as [t' [Ha Hb]].
           apply H3 in Ha. contradict Ha. auto.
      * exists (S x1). cbn. unfold ex_sub_ex. destruct (ex_sub_len _ _) as [[|] [e He]].
        ** rewrite list_step_correct. rewrite H0. cbn. apply H3.
        ** rewrite<- itp_correct in He. rewrite extend_start in He. cbn in *.
           assert (exists n, ex_subtype (current a it1) b (iterator_to_path b (start_iterator b)) n = Some false).
           { exists e. auto. } rewrite<- ex_sub_corr_ieq in H4. destruct H4. clear H4.
           eapply x in H1; [|apply in_eq]. destruct H1 as [t' [Ha Hb]].
           specialize (x2 t' _ (iterator_has_clauses _)). apply x2 in Ha. contradict Ha. auto.
  - induction it using iter_rect.
    + destruct (forall_iter_inner a b it).
      * eexists; eauto.
      * destruct H as [n Hrm].
        destruct n; cbn in Hrm; unfold ex_sub_ex in Hrm; destruct (ex_sub_len _ _) in Hrm;
          rewrite list_step_correct in Hrm; rewrite H0 in Hrm; cbn in Hrm;
           destruct x; try (inject Hrm); rewrite<- itp_correct in e0;
           destruct (nonempty_rem _ it); pose proof (next_empty _ _ _ H0 H);
           inject H1;  inject H2; apply e in H; destruct H as [t' [Ha Hb]];
           inject Ha; try (inject H); rewrite extend_start in e0; cbn in e0;
           rewrite<- ex_sub_corr_eq in e0; destruct e0; clear H; destruct x;
           destruct (a0 _ (iterator_has_clauses b)); apply Hb in H; apply H in H1;
           inversion H1.
    + destruct (forall_iter_inner a b it1).
      * eexists; eauto.
      * exfalso. destruct (nonempty_rem _ it1). pose proof (next_step_next _ _ _ _ _ H1 H0).
        destruct H. destruct x0; cbn in *; try (inject H);
                      unfold ex_sub_ex in H; destruct (ex_sub_len _ _) in H.
        ** destruct x0; [|inject H]. rewrite list_step_correct in H. rewrite H0 in H.
           cbn in H. inject H.
        ** destruct x1.
           *** rewrite<- itp_correct in e0.  rewrite extend_start in e0. cbn in e0.
               rewrite<- ex_sub_corr_eq in e0. destruct e0. destruct x1. clear H3.
               apply e in H1. destruct H1 as [t [Ha Hb]]. inject Ha.
               **** destruct(a0 _ (iterator_has_clauses _)). apply Hb in H1.
                    apply H1 in H3. inject H3.
               **** rewrite list_step_correct in H. rewrite H0 in H. cbn in H.
                    assert ((exists n : nat, fa_ex_subtype a b (iterator_to_path a it2) n = Some true)).
                    { eexists. eauto. }
                    apply IHit1 in H3. clear IHit1. destruct H3. eapply x2 with (t:=t) in H2; auto.
                    destruct H2 as [t' [Hc Hd]]. apply Hb in Hc. apply Hc in Hd. inject Hd.
           *** inject H. 
Qed.

(* ibid, now for nontrue results *)
Lemma fa_sub_always_ne : forall a b it,
    (forall m, fa_ex_subtype a b (iterator_to_path a it) m <> Some true)
    <-> (exists n, fa_ex_subtype a b (iterator_to_path a it) n = Some false).
Proof.
  intros. split.
  - induction it using iter_rect; intros H0.
    + pose proof (H0 0). clear H0. cbn in H1. rewrite list_step_correct in H1; rewrite H in H1; cbn in *.
      destruct (ex_sub_ex _) eqn:Hese; try (contradiction). exists 0. cbn. rewrite Hese. auto.
    + destruct (ex_sub_ex (fst (lookup_path a (iterator_to_path a it1))) b) eqn:Hese.
      * destruct (IHit1).
        ** intros. pose proof (H0 (S m)). cbn in H1. rewrite Hese in H1.
           rewrite list_step_correct in H1. rewrite H in H1. cbn in H1. auto.
        ** exists (S x). cbn. rewrite Hese. rewrite list_step_correct. rewrite H. cbn. auto.
      * exists 0. cbn. rewrite Hese. auto.
  - intros H0. destruct H0. generalize dependent x. induction it using iter_rect; intros. 
    + destruct x; cbn in H0; rewrite list_step_correct in H0; rewrite H in H0; cbn in H0;
        destruct (ex_sub_ex _) eqn:Hese in H0; try (inject H0);
          destruct m; cbn; rewrite Hese; intro; try (inject H1); try (inject H0).
    + destruct x.
      * cbn in H0. rewrite list_step_correct in H0; rewrite H in H0; cbn in H0.
        destruct (ex_sub_ex _) eqn:Hese in H0; try (inject H0).
        destruct m; cbn; rewrite Hese; intro; inject H1.
      * cbn in H0. rewrite list_step_correct in H0; rewrite H in H0; cbn in H0.
        destruct (ex_sub_ex _) eqn:Hese in H0.
        ** destruct m.
           *** cbn in *. rewrite Hese in *. rewrite list_step_correct; rewrite H; cbn. intro. inject H1.
           *** eapply IHit1 in H0. cbn. rewrite Hese. rewrite list_step_correct; rewrite H; cbn. apply H0.
        ** destruct m; cbn; rewrite Hese; try (intro; inject H1; fail).         
Qed.

(* ibid *)
Lemma fa_sub_corr_ieq : forall a b it,
    (exists pf, forall_iter_inner a b it = right pf) <->
    exists n, fa_ex_subtype a b (iterator_to_path a it) n = Some false.
Proof.
  intros. pose proof (fa_sub_corr_eq a b it). apply not_iff_compat in H.
  repeat rewrite neg_exists_is_forall in H. split.
  - intros. destruct H0. apply fa_sub_always_ne. apply H. rewrite H0. intros. intro. inject H1. 
  - intros. rewrite fa_sub_always_ne in H. rewrite<- H in H0. destruct (forall_iter_inner a b it).
    + pose proof (H0 e). exfalso. apply H1. auto.
    + exists e. auto.
Qed.

(* there exists some amount of fuel that will get a computable answer r out of
   fa_ex_subtype *)
Lemma ex_fa_ex (a b : type) :
  { r | exists n, fa_ex_subtype a b (fst (extend_list a nil)) n = Some r}.
Proof.
  intros. remember (fst (extend_list a nil)). rewrite extend_start in Heql.
  cbn in *. remember (start_iterator a). clear Heqt. subst. induction t using iter_rect.
  - destruct (ex_sub_ex (fst (lookup_path a (iterator_to_path a t))) b) eqn:Hex.
    + exists true. exists (S 0). cbn. rewrite Hex. rewrite list_step_correct.
      rewrite H. cbn. auto.
    + exists false. exists (S 0). cbn. rewrite Hex. auto. 
  - destruct IHt1. destruct x.
    + destruct (ex_sub_ex (fst (lookup_path a (iterator_to_path a t1))) b) eqn:Hese.
      * exists true. destruct e. exists (S x). cbn in *. rewrite Hese.
        rewrite list_step_correct. rewrite H. cbn. auto.
      * exists false. destruct e. exists (S 0). cbn. rewrite Hese. auto.
    + exists false. destruct e. exists (S x). cbn. rewrite list_step_correct. rewrite H.
      cbn. rewrite H0.
      destruct (ex_sub_ex (fst (lookup_path a (iterator_to_path a t1))) b) eqn:Hese; auto. 
Qed.

(* we can use the stack representation of types to conclude subtyping, just as the other two did *)
Definition stack_subtype (a b: type) : {NormalSubtype a b} + {~NormalSubtype a b}.
Proof.
  intros. destruct (ex_fa_ex a b). rewrite extend_start in e. cbn in e. destruct x.
  - rewrite<- fa_sub_corr_eq in e.
    left. destruct e. pose proof (x (clauses a) (iterator_has_clauses a)).
    unfold NormalSubtype. intros. rewrite<- clauses_in_type in H1. apply H0 in H1.
    destruct H1. exists x0. rewrite<- clauses_in_type. auto.
  - rewrite<- fa_sub_corr_ieq in e. right.
    destruct e. pose proof (x (clauses a) (iterator_has_clauses a)).
    unfold NormalSubtype. intro. destruct H0 as [t [Ha Hb]].  rewrite clauses_in_type in Ha.
    apply H1 in Ha. destruct Ha as [t' [Hc Hd]]. rewrite<- clauses_in_type in Hc. apply Hb in Hc.
    apply Hc in Hd. inversion Hd.
Qed.