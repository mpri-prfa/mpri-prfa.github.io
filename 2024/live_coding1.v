(** Live coding session for the first lecture

  The goal is to show you how one uses Coq.
  We will start with very easy stuff. Don't worry we have more advanced stuff
  for you as well.

**)

(** We open a section to be able to introduce variables.
    You can mostly ignore it for now.
**)
Section Live.

  (** We assume we have some propositions named P and Q **)
  Context (P Q : Prop).

  (** Implication is written -> (not =>!) **)

  Lemma P_imp_P : P -> P.
  Proof.
    (* The goal is P -> P, P implies P. *)
    (* To prove it, we can assume we have a proof of P, we call it h. *)
    intro h.
    (* We now have to prove P, but notice we have some extra assumption h : P *)
    (* To use an assumption, one can use the apply tactic: *)
    apply h.
    (* Proof finished! All that's left to do is to type Qed. *)
  Qed.

  (* We now have a new fact: P_imp_P which is a proof of P -> P *)
  (* You can check this fact using the About command *)
  About P_imp_P.

  (** We can also write conjunction (/\) and disjunction (\/) **)

  Lemma and_comm : P /\ Q -> Q /\ P.
  Proof.
    (* We have an implication so we use intro. *)
    intro h.
    (* We now have P /\ Q and we need to prove Q /\ P *)
    (** First we need to have a look at P /\ Q, we would like to turn it into
        two different hyoptheses: one for P and for Q.
        We can use the destruct tactic to decompose an hypothesis.
    **)
    destruct h as [hP hQ].
    (** To prove a conjunction we can use split to let us prove the two parts
        independently.
    **)
    split.
    (* Notice we now have two goals, P and Q. *)
    (* We use bullets to focus on the goals one by one. *)
    - (* Now proving Q is easy. *)
      apply hQ.
    - apply hP.
  Qed.

  Lemma or_comm : P \/ Q -> Q \/ P.
  Proof.
    intro h.
    (* Now we first need to do a case analysis on whether P or Q holds. *)
    (* This is done using destruct as well. *)
    destruct h as [hP | hQ].
    (* Notice how we used a pipe to separate the two cases. *)
    - (* Now we have P and we want to prove Q \/ P *)
      (* We can use the tactic right to say we want to prove the right case. *)
      right.
      apply hP.
    - (* You can guess the dual is left *)
      left.
      apply hQ.
  Qed.

  (** You also have the usual ⊤ and ⊥ which in Coq are called True and False **)

  Lemma truetrue : True.
  Proof.
    (* To prove it, you can also use split! It's like the nullary conjunction *)
    split.
  Qed.

  Lemma falsefalse : False.
  Proof.
    (* This one you cannot prove! *)
    (* So we give up. *)
  Abort.

  (** However, False implies anything: ex falso quodlibet **)

  Lemma anything_goes : False -> P.
  Proof.
    intro bot.
    (* The exfalso tactic concludes anything as long as you can prove False *)
    exfalso.
    apply bot.
    (* Let's do the proof again, with an alternative approach *)
  Restart.
    (** Namely, we can do case analysis on all possible proofs of False
        directly—of which there are none.
    **)
    intro bot.
    destruct bot.
  Qed.

  (** Let us have a look at negation now.
      ~ P is a notation for the negation of P.
      In fact it is defined as P -> False, so we can use intro to prove a
      negation.
  **)

  Lemma nofalse : ~ False.
  Proof.
    intro contra. apply contra.
  Qed.

  (* Let us consider the type of booleans, with elements true and false *)
  Lemma negb_true :
    negb true = false.
  Proof.
    (* Here we have computation, so we can ask Coq to simplify things *)
    simpl. reflexivity.
  Qed.

  (* We show that boolean negation is involutive *)
  Context (b : bool).

  Lemma negb_invol :
    negb (negb b) = b.
  Proof.
    (** Similar to how destruct can be used to do case analysis on hypotheses,
        it can be used to do case analysis on booleans.
    **)
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  (* We now turn to boolean conjunction *)
  Context (b1 b2 : bool).

  Lemma andb_comm :
    andb b1 b2 = andb b2 b1.
  Proof.
    destruct b1.
    - simpl. destruct b2.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - simpl. destruct b2.
      + simpl. reflexivity.
      + simpl. reflexivity.
  Qed.

  Lemma andb_comm' :
    andb b1 b2 = andb b2 b1.
  Proof.
    (* We can also ask Coq to do two case analyses at the same time *)
    destruct b1, b2.
    - (* No need to use simpl every time, reflexivity does it on its own *)
      reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* Let us switch to natural numbers. *)

  Context (n : nat).

  Lemma calc_12_3 : 12 + 3 = 15.
  Proof.
    (* Here we have computation again, so we can ask Coq to simplify things *)
    simpl.
    (* Now we have to prove 15 = 15, the is true by reflexivity of equality *)
    reflexivity.
  Qed.

  Lemma double_eq : n + n = 2 * n.
  Proof.
    (* Coq can compute also a bit, even with variables *)
    simpl.
    (** The + 0 at the end might seem surprising.
        This has to do with the definition of multiplication:
          0 * m := 0
          (n + 1) * m := m + n * m

        So 2 * m = m + 1 * m = m + (m + (0 * m)) = m + (m + 0).

        Another surprise is that n + 0 does not compute to n.
        That's because of the definition of addition:
          0 + m := m
          (n + 1) + m := (n + m) + 1
        It looks at its left argument first, and here it gives up because it's
        a variable.
    **)
    (* So what can we do now? *)
    (** To prove an equality, we can use the fact that it is a congruence
        using the f_equal tactic.
    **)
    f_equal.
    (* Now we can prove this property by induction on n. *)
    induction n.
    (* We have two cases to prove, the case n = 0 and the case n + 1 *)
    (* In Coq, the successor of n is written S n, like in Peano arithmetic. *)
    - (* Now, 0 + 0 is something Coq knows: *)
      simpl. reflexivity.
    - (** Here, S n0 is not a variable, but it's not a concrete natural number
          either. Coq will be able to simplify it a bit.
      **)
      simpl.
      (* We have S on both sides *)
      f_equal.
      (* Here we can apply our induction hypothesis. *)
      (** Since we did not chose its name, we can use a different tactic
          that finds a matching hypothesis on its own:
      **)
      assumption.
  Qed.

  Fixpoint double (n : nat) :=
    match n with
    | 0 => 0
    | S n => S (S (double n))
    end.

  Lemma double_eq2 : double n = n * 2.
  Proof.
    induction n as [ | m].
    - simpl. reflexivity.
    - simpl. rewrite IHm. reflexivity.
  Qed.

End Live.
