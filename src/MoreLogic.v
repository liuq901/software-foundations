(** * MoreLogic: More on Logic in Coq *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists)  *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There is a [nat] n which (S n) is beautiful. *)

(*
*)
(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  unfold not.
  intros X P H1 H2.
  inversion H2 as [x H3].
  apply H3.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  unfold not.
  intros H1 X P H2 x.
  assert (H3 : P x \/ (P x -> False)).
    apply H1.
  inversion H3 as [H4 | H5].
  apply H4.
  apply ex_falso_quodlibet.
  apply H2.
  exists x.
  apply H5.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  Case "->".
    intros H1.
    inversion H1 as [x H2].
    inversion H2 as [H3 | H3].
    left.
    exists x.
    apply H3.
    right.
    exists x.
    apply H3.
  Case "<-".
    intros H1.
    inversion H1 as [H2 | H2].
    inversion H2 as [x H3].
    exists x.
    left.
    apply H3.
    inversion H2 as [x H3].
    exists x.
    right.
    apply H3.
Qed.
(** [] *)

(* ###################################################### *)
(** * Evidence-Carrying Booleans *)

(** So far we've seen two different forms of equality predicates:
    [eq], which produces a [Prop], and the type-specific forms, like
    [beq_nat], that produce [boolean] values.  The former are more
    convenient to reason about, but we've relied on the latter to let
    us use equality tests in _computations_.  While it is
    straightforward to write lemmas (e.g. [beq_nat_true] and
    [beq_nat_false]) that connect the two forms, using these lemmas
    quickly gets tedious. *)

(** *** *)
(** It turns out that we can get the benefits of both forms at once by
    using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
    of its values being just [true] and [false], they carry _evidence_
    of truth or falsity. This means that when we [destruct] them, we
    are left with the relevant evidence as a hypothesis -- just as
    with [or].  (In fact, the definition of [sumbool] is almost the
    same as for [or].  The only difference is that values of [sumbool]
    are declared to be in [Set] rather than in [Prop]; this is a
    technical distinction that allows us to compute with them.) *)

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Read as a theorem, this says that equality on [nat]s is decidable:
    that is, given two [nat] values, we can always produce either
    evidence that they are equal or evidence that they are not.  Read
    computationally, [eq_nat_dec] takes two [nat] values and returns a
    [sumbool] constructed with [left] if they are equal and [right] if
    they are not; this result can be tested with a [match] or, better,
    with an [if-then-else], just like a regular [boolean].  (Notice
    that we ended this proof with [Defined] rather than [Qed].  The
    only difference this makes is that the proof becomes
    _transparent_, meaning that its definition is available when Coq
    tries to do reductions, which is important for the computational
    interpretation.) *) 

(** *** *)
(** Here's a simple example illustrating the advantages of the
   [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the
    version of [override] defined using [beq_nat], where we had to use
    the auxiliary lemma [beq_nat_true] to convert a fact about
    booleans to a Prop. *)

(** **** Exercise: 1 star (override_shadow')  *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  unfold override'.
  intros X x1 x2 k1 k2 H.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2".
    reflexivity.
  Case "k1 <> k2".
    reflexivity.
Qed.
(** [] *)





(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P nil
  | all_app : forall n l, all X P l -> P n -> all X P (n :: l)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem all_forallb : forall (X : Type) (f : X -> bool) (l : list X),
  forallb f l = true <-> all X (fun x => f x = true) l.
Proof.
  intros X f l.
  split.
  Case "->".
    intros H.
    induction l as [| x l'].
    SCase "l = nil".
      apply all_nil.
    SCase "l = x :: l'".
      apply all_app.
      apply IHl'.
      simpl in H.
      apply andb_true_elim2 in H.
      apply H.
      apply andb_true_elim1 in H.
      apply H.
  Case "<-".
    intros H.
    induction H as [| x l'].
    SCase "l = nil".
      reflexivity.
    SCase "l = x :: l'".
      simpl.
      rewrite -> H0.
      rewrite -> IHall.
      reflexivity.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Inductive merge {X : Type} : list X -> list X -> list X -> Prop :=
  | merge_nil : merge nil nil nil
  | merge_l : forall n l l1 l2, merge l l1 l2 -> merge (n :: l) (n :: l1) l2
  | merge_r : forall n l l1 l2, merge l l1 l2 -> merge (n :: l) l1 (n :: l2).

Theorem filter_challenge : forall (X : Type) (f : X -> bool) (l l1 l2: list X),
  merge l l1 l2 -> all X (fun x => f x = true) l1 -> 
  all X (fun x => f x = false) l2 -> filter f l = l1.
Proof.
  intros X f l l1 l2 H1 H2 H3.
  induction H1.
  Case "merge_nil".
    reflexivity.
  Case "merge_l".
    simpl.
    inversion H2.
    rewrite -> H5.
    apply f_equal.
    apply IHmerge.
    apply H4.
    apply H3.
  Case "merge_r".
    simpl.
    inversion H3.
    rewrite -> H5.
    apply IHmerge.
    apply H2.
    apply H4.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Inductive subseq {X : Type} : list X -> list X -> Prop :=
  | sub_nil : subseq nil nil
  | sub_addr : forall n l1 l2, subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_addl : forall n l1 l2, subseq l1 l2 -> subseq (n :: l1) (n :: l2).

Lemma subseq_length : forall (X : Type) (l1 l2 : list X),
  subseq l1 l2 -> length l1 <= length l2.
Proof.
  intros X l1 l2 H.
  induction H.
  Case "sub_nil".
    apply le_n.
  Case "sub_addr".
    simpl.
    apply le_S.
    apply IHsubseq.
  Case "sub_addl".
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHsubseq.
Qed.

Lemma le_false : forall n : nat, S n <= n -> False.
Proof.
  intros n H.
  induction n as [| n'].
  Case "n = 0".
    inversion H.
  Case "n = S n'".
    apply IHn'.
    apply Sn_le_Sm__n_le_m.
    apply H.
Qed.

Lemma subseq_length_eq : forall (X : Type) (l1 l2 : list X),
  subseq l1 l2 -> length l2 <= length l1 -> l1 = l2.
Proof.
  intros X l1 l2 H1 H2.
  induction H1.
  Case "sub_nil".
    reflexivity.
  Case "sub_addr".
    apply subseq_length in H1.
    simpl in H2.
    assert (H3 : S (length l2) <= length l2).
      apply le_trans with (length l1).
      apply H2.
      apply H1.
    apply le_false in H3.
    inversion H3.
  Case "sub_addl".
    apply f_equal.
    apply IHsubseq.
    simpl in H2.
    apply Sn_le_Sm__n_le_m.
    apply H2.
Qed.

Lemma filter_subseq : forall (X : Type) (f : X -> bool) (l l' : list X),
  all X (fun x => f x = true) l' -> subseq l' l -> subseq l' (filter f l).
Proof.
  intros X f l l' H1 H2.
  induction H2.
  Case "sub_nil".
    apply sub_nil.
  Case "sub_addr".
    simpl.
    destruct (f n).
    apply sub_addr.
    apply IHsubseq.
    apply H1.
    apply IHsubseq.
    apply H1.
  Case "sub_addl".
    simpl.
    inversion H1.
    rewrite -> H4.
    apply sub_addl.
    apply IHsubseq.
    apply H3.
Qed.

Lemma filter_all : forall (X : Type) (f : X -> bool) (l : list X),
  all X (fun x => f x = true) (filter f l) /\ subseq (filter f l) l.
Proof.
  split.
  Case "left".
    induction l as [| x l'].
    SCase "l = nil".
      apply all_nil.
    SCase "l = x :: l'".
      simpl.
      destruct (f x) eqn:H.
      apply all_app.
      apply IHl'.
      apply H.
      apply IHl'.
  Case "right".
    induction l as [| x l'].
    SCase "l = nil".
      apply sub_nil.
    SCase "l = x :: l'".
      simpl.
      destruct (f x).
      apply sub_addl.
      apply IHl'.
      apply sub_addr.
      apply IHl'.
Qed.

Theorem filter_challenge_2 : forall (X : Type) (f : X -> bool) (l l' : list X),
  all X (fun x => f x = true) l' -> subseq l' l -> (forall l'' : list X, 
  all X (fun x => f x = true) l'' -> subseq l'' l -> length l'' <= length l') ->
  filter f l = l'.
Proof.
  intros X f l l' H1 H2 H3.
  symmetry.
  apply subseq_length_eq.
  apply filter_subseq.
  apply H1.
  apply H2.
  apply H3.
  apply filter_all.
  apply filter_all.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs ys x H.
  induction xs as [| h t].
  Case "xs = nil".
    right.
    apply H.
  Case "xs = h :: t".
    inversion H.
    left.
    apply ai_here.
    apply IHt in H1.
    inversion H1.
    left.
    apply ai_later.
    apply H3.
    right.
    apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x H.
  induction xs as [| h t].
  Case "xs = nil".
    inversion H.
    inversion H0.
    apply H0.
  Case "xs = h :: t".
    inversion H.
    inversion H0.
    apply ai_here.
    simpl.
    apply ai_later.
    apply IHt.
    left.
    apply H2.
    simpl.
    apply ai_later.
    apply IHt.
    right.
    apply H0.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint {X : Type} (l1 l2 : list X) : Prop := forall (x : X), 
  (appears_in x l1 -> ~ appears_in x l2) /\ (appears_in x l2 -> ~ appears_in x l1).

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {X : Type} : list X -> Prop :=
  | np_nil : no_repeats nil
  | np_app : forall x l, no_repeats l -> ~ appears_in x l -> no_repeats (x :: l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Lemma no_repeats_not_appears_in : forall (X : Type) (l : list X) (x : X),
  no_repeats (x :: l) -> ~ appears_in x l.
Proof.
  unfold not.
  intros X l x H1 H2.
  destruct H2.
  Case "ai_here".
    inversion H1.
    apply H3.
    apply ai_here.
  Case "ai_later".
    inversion H1.
    inversion H3.
    apply H4.
    apply ai_later.
    apply H2.
Qed.

Lemma disjoint_not_appears_in : forall (X : Type) (l1 l2 : list X) (x : X),
  disjoint (x :: l1) l2 -> ~ appears_in x l2.
Proof.
  intros X l1 l2 x H.
  apply H.
  apply ai_here.
Qed.

Lemma not_appears_in_app : forall (X : Type) (l1 l2 : list X) (x : X),
  ~ appears_in x l1 -> ~ appears_in x l2 -> ~ appears_in x (l1 ++ l2).
Proof.
  unfold not.
  intros X l1 l2 x H1 H2 H3.
  apply appears_in_app in H3.
  destruct H3.
  apply H1 in H.
  apply H.
  apply H2 in H.
  apply H.
Qed.

Theorem no_repeats_disjoint : forall (X : Type) (l1 l2 : list X),
  no_repeats l1 -> no_repeats l2 -> disjoint l1 l2 -> no_repeats (l1 ++ l2).
Proof.
  induction l1 as [| x l'].
  Case "l1 = nil".
    intros.
    apply H0.
  Case "l1 = x :: l'".
    intros.
    simpl.
    apply np_app.
    apply IHl'.
    inversion H.
    apply H4.
    apply H0.
    split.
    intros.
    apply H1.
    apply ai_later.
    apply H2.
    intros.
    assert (~ appears_in x0 (x :: l')).
      apply H1.
      apply H2.
    unfold not.
    intros.
    apply H3.
    apply ai_later.
    apply H4.
    apply not_appears_in_app.
    apply no_repeats_not_appears_in.
    apply H.
    apply disjoint_not_appears_in with l'.
    apply H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars (nostutter)  *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1;4;1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | ns_nil : nostutter nil
  | ns_one : forall x, nostutter [x]
  | ns_app : forall x y l, nostutter (y :: l) -> x <> y -> nostutter (x :: y :: l)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. 
  apply ns_app. apply ns_app. apply ns_app. apply ns_app. apply ns_app. apply ns_one.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
  unfold not. intros. inversion H.
Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. apply ns_nil.  Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. apply ns_one.  Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H2.
  apply H9.
  reflexivity.
Qed.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof.
  intros X l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l H.
  induction H.
  Case "ai_here".
    exists nil.
    exists l.
    reflexivity.
  Case "ai_later".
    inversion IHappears_in as [l1 H1].
    inversion H1 as [l2 H2].
    rewrite -> H2.
    exists (b :: l1).
    exists l2.
    reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_here : forall x l, appears_in x l -> repeats (x :: l)
  | rep_later : forall x l, repeats l -> repeats (x :: l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1'].
   Case "l1 = nil".
     intros.
     inversion H1.
   Case "l1 = x :: l1'".
     unfold excluded_middle.
     intros.
     assert (appears_in x l1' \/ ~ appears_in x l1').
       apply H.
     destruct H2.
     apply rep_here.
     apply H2.
     apply rep_later.
     assert (appears_in x l2).
       apply H0.
       apply ai_here.
     apply appears_in_app_split in H3.
     destruct H3 as [l4 [l5]].
     intros.
     apply IHl1' with (l4 ++ l5).
     unfold excluded_middle.
     apply H.
     intros.
     assert (appears_in x0 (x :: l1')).
       apply ai_later.
       apply H4.
     apply H0 in H5.
     rewrite -> H3 in H5.
     apply appears_in_app in H5.
     destruct H5.
     apply app_appears_in.
     left.
     apply H5.
     apply app_appears_in.
     right.
     inversion H5.
     apply ex_falso_quodlibet.
     apply H2.
     rewrite <- H7.
     apply H4.
     apply H7.
     rewrite -> H3 in H1.
     rewrite -> app_length in H1.
     simpl in H1.
     unfold lt in H1.
     rewrite <- plus_n_Sm in H1.
     apply Sn_le_Sm__n_le_m in H1.
     rewrite -> app_length.
     apply H1.
Qed.
(** [] *)



(** $Date: 2014-12-31 16:01:37 -0500 (Wed, 31 Dec 2014) $ *)
