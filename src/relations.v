Require Import SubtypeCorrectness.syntax.
Inductive BaseSubtype: type -> type -> Prop :=
| BSAtom : forall i, BaseSubtype (atom i) (atom i)
| BSTuple1 : forall ts1 ts2, BaseSubtype ts1 ts2 -> BaseSubtype (tuple1 ts1) (tuple1 ts2)
| BSTuple2 : forall ts1 ts2 ts1' ts2', BaseSubtype ts1 ts2 -> BaseSubtype ts1' ts2' ->
                                       BaseSubtype (tuple2 ts1 ts1') (tuple2 ts2 ts2').

Inductive InType : type -> type -> Prop :=
| IAtom : forall i, InType (atom i) (atom i)
| ITuple1 : forall ts ts', InType ts ts' ->  InType (tuple1 ts) (tuple1 ts')
| ITuple2 : forall ts1 ts2 ts1' ts2', InType ts1 ts1' -> InType ts2 ts2' ->
                                      InType (tuple2 ts1 ts2) (tuple2 ts1' ts2')
| IUnionL : forall t1 t2 t3, InType t1 t2 -> InType t1 (union t2 t3)
| IUnionR : forall t1 t2 t3, InType t1 t3 -> InType t1 (union t2 t3).

Definition NormalSubtype(t1 t2:type):Prop :=
  forall t'1, InType t'1 t1 -> exists t'2, InType t'2 t2 /\ BaseSubtype t'1 t'2.
