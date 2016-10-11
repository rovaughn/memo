Require Export Map.
Require Export List.

(* A syscall is something a program calls to modify its environment or make
   a query.  A syscall also returns a result (or potentially kills the program.
*)

Definition Component := nat.
Definition Path := list Component.
Definition Data := nat.
Definition ExitStatus := bool.

Inductive Files :=
| Dir : Map Component Files -> Files
| File : Data -> Files
.

Inductive ReadResult :=
| ReadIsDir : ReadResult
| ReadNoPath : ReadResult
| ReadNoEnt : ReadResult
| ReadNotDir : ReadResult
| ReadSuccess : Data -> ReadResult
.

Inductive WriteResult :=
| WriteIsDir : WriteResult
| WriteNoPath : WriteResult
| WriteNotDir : WriteResult
| WriteSuccess : WriteResult
.

Definition eqcomp: Component -> Component -> bool := Nat.eqb.

Fixpoint read (path : Path) (files : Files): ReadResult :=
match path, files with
| nil, File data => ReadSuccess data
| nil, Dir _ => ReadIsDir
| _ :: _, File _ => ReadNotDir
| name :: path', Dir entries =>
  match lookup eqcomp name entries with
  | Some files' => read path' files'
  | None =>
    match path' with
    | _ :: _ => ReadNoPath
    | _      => ReadNoEnt
    end
  end
end.

Fixpoint write path data files: WriteResult * Files :=
match path, files with
| nil, File _ => (WriteSuccess, File data)
| nil, Dir _ => (WriteIsDir, files)
| _ :: _, File _ => (WriteNotDir, files)
| name :: path', Dir entries =>
  match lookup eqcomp name entries with
  | None =>
    match path' with
    | nil => (WriteSuccess, Dir (insert eqcomp name (File data) entries))
    | _   => (WriteNoPath, files)
    end
  | Some subfiles =>
    let (wr, subfiles') := write path' data subfiles
    in (wr, Dir (insert eqcomp name subfiles' entries))
  end
end.

Definition exfs := Dir ((1, File 1) :: (2, File 2) :: (3, File 3) :: nil).

Example ex1 : read (1::nil) exfs = ReadSuccess 1. reflexivity. Qed.
Example ex2 : read (2::nil) exfs = ReadSuccess 2. reflexivity. Qed.
Example ex3 : read (3::nil) exfs = ReadSuccess 3. reflexivity. Qed.
Example ex4 : read (4::nil) exfs = ReadNoEnt. reflexivity. Qed.
Example ex5 : write (1::nil) 5 exfs = (WriteSuccess, Dir ((1, File 5) :: (2, File 2) :: (3, File 3) :: nil)). reflexivity. Qed.
Example ex6 : write (4::nil) 4 exfs = (WriteSuccess, Dir ((1, File 1) :: (2, File 2) :: (3, File 3) :: (4, File 4) :: nil)). simpl. reflexivity. Qed.

Inductive Program :=
| Read : Path -> (ReadResult -> Program) -> Program
| Write : Path -> Data -> (WriteResult -> Program) -> Program
| Exit : ExitStatus -> Program
.

Inductive Trace :=
| TRead : Path -> ReadResult -> Trace
| TWrite : Path -> Data -> WriteResult -> Trace
| TExit : ExitStatus -> Trace
.

(* equivalent to ; in bash.  followed_by a b executes a then b, regardless of
   a's exit status. *)
Fixpoint followed_by a b :=
match a with
| Read path next => Read path (fun rr => followed_by (next rr) b)
| Write path data next => Write path data (fun rr => followed_by (next rr) b)
| Exit _ => b
end.

(* equivalent to && in bash.  and_then a b executes a and if it's successful
   also executes b. *)
Fixpoint and_then a b :=
match a with
| Read path next => Read path (fun rr => and_then (next rr) b)
| Write path data next => Write path data (fun rr => and_then (next rr) b)
| Exit true => b
| Exit false => Exit false
end.

(* equivalent to || in bash.  or_else a b executes a and only if it fails
   executes b. *)
Fixpoint or_else a b :=
match a with
| Read path next => Read path (fun rr => or_else (next rr) b)
| Write path data next => Write path data (fun rr => or_else (next rr) b)
| Exit true => Exit true
| Exit false => b
end.

(* produce the trace log from running a program. *)
Fixpoint trace program files: list Trace :=
match program with
| Read path next =>
  let rr := read path files
  in TRead path rr :: trace (next rr) files
| Write path data next =>
  let (wr, files') := write path data files
  in TWrite path data wr :: trace (next wr) files'
| Exit e => TExit e :: nil
end.

Fixpoint exit program files :=
match program with
| Read path next => exit (next (read path files)) files
| Write path data next =>
  let (wr, files') := write path data files
  in exit (next wr) files'
| Exit e => e
end.

Fixpoint run program files: Files :=
match program with
| Read path next => run (next (read path files)) files
| Write path data next =>
  let (wr, files') := write path data files
  in run (next wr) files'
| Exit e => files
end.

Definition cp from to := Read from (fun rr => match rr with
| ReadSuccess data => Write to data (fun wr => match wr with
  | WriteSuccess => Exit true
  | _            => Exit false
  end)
| _ => Exit false
end
).

Definition ex: Program := and_then (cp (1::nil) (2::nil)) (cp (3::nil) (4::nil)).

Compute (run ex exfs).
Compute (trace ex exfs).
Definition program_eq a a' := forall f, run a f = run a' f.

Notation "A ~ B" := (program_eq A B) (at level 86).

Lemma program_eq_refl: forall a, a ~ a.
Proof. unfold program_eq. induction a.
- simpl. intros. apply H.
- simpl. intros. destruct (write p d f). apply H.
- simpl. tauto.
Qed.

Lemma program_eq_run: forall a b,
a ~ b <-> forall f, run a f = run b f.
Proof. split.
- intros. apply H.
- intros. unfold program_eq. apply H.
Qed.

Lemma program_eq_trans: forall a b c,
a ~ b -> b ~ c -> a ~ c.
Proof.
intros. unfold program_eq in H. unfold program_eq in H0. unfold program_eq.
intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma program_eq_comm: forall a b,
a ~ b -> b ~ a.
Proof.
intros. unfold program_eq. unfold program_eq in H.
intros. symmetry. apply H.
Qed.

Definition trivial_memo (log : list Trace) (program : Program): Program := program.

Lemma trivial_memo_correct : forall a w, trivial_memo (trace a w) a ~ a.
Proof. unfold program_eq. unfold trivial_memo. tauto. Qed.

Definition rreq r1 r2 :=
match r1, r2 with
| ReadIsDir, ReadIsDir => true
| ReadNoEnt, ReadNoEnt => true
| ReadNotDir, ReadNotDir => true
| ReadNoPath, ReadNoPath => true
| ReadSuccess d1, ReadSuccess d2 => Nat.eqb d1 d2
| _, _ => false
end.

Lemma rreq_eq: forall r1 r2, rreq r1 r2 = true <-> r1 = r2.
Proof. split.
- destruct r1, r2.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. simpl in H. apply PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
- intros. rewrite H. destruct r2.
  auto. auto. auto. auto. simpl. apply PeanoNat.Nat.eqb_refl.
Qed.

Lemma rreq_ne: forall r1 r2, rreq r1 r2 = false <-> r1 <> r2.
Proof. split.
- destruct r1, r2.
  + intros. inversion H. + congruence. + congruence. + congruence. + congruence. + congruence.
  + intros. inversion H. + congruence. + congruence. + congruence. + congruence. + congruence.
  + intros. inversion H. + congruence. + congruence. + congruence. + congruence. + congruence.
  + intros. inversion H. + congruence. + congruence. + congruence. + congruence. + congruence.
  + intros. apply PeanoNat.Nat.eqb_neq in H. congruence.
- intros. destruct r1, r2.
  + congruence. + reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
  + congruence. + reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
  + congruence. + reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
  + congruence. + reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
  + generalize dependent H. induction d, d0.
    * intros. congruence. * intros. reflexivity. * intros. reflexivity.
    * simpl. intros. apply PeanoNat.Nat.eqb_neq. congruence.
Qed.

Definition wreq d w r: bool :=
match w, r with
| WriteIsDir, ReadIsDir => true
| WriteNoPath, ReadNoPath => true
| WriteNotDir, ReadNotDir => true
| WriteSuccess, ReadSuccess d' => Nat.eqb d d'
| _, _ => false
end.

Lemma pair_eq: forall (A B : Type) (a c : A) (b d : B),
a = c -> b = d -> (a, b) = (c, d).
Proof. intros. rewrite H. rewrite H0. reflexivity. Qed.

Lemma eqcomp_eq: forall x y, eqcomp x y = true -> x = y.
Proof. unfold eqcomp. intros. apply PeanoNat.Nat.eqb_eq. apply H. Qed.

Lemma wreq_correct: forall p f w d,
wreq d w (read p f) = true -> write p d f = (w, f).
Proof. induction p.
- intros. simpl. simpl in H. destruct f.
  + destruct w. * congruence. * inversion H. * inversion H. * inversion H.
  + destruct w.
    * inversion H. * inversion H. * inversion H.
    * apply pair_eq. congruence. simpl in H. apply PeanoNat.Nat.eqb_eq in H.
      rewrite H. congruence.
- induction f.
  + intros. simpl. simpl in H. destruct (lookup eqcomp a m) eqn:Hl.
    * destruct (write p d f) eqn:Hw. apply IHp in H. rewrite H in Hw. inversion Hw. apply pair_eq.
      { congruence. }
      { replace (insert eqcomp a f0 m) with m. congruence.
        symmetry. apply map_reeinsert. apply eqcomp_eq. rewrite <- H2. apply Hl. }
    * destruct p.
      { destruct w. inversion H. inversion H. inversion H. inversion H. }
      { destruct w. inversion H. congruence. inversion H. inversion H. }
  + intros. simpl. simpl in H. destruct w. inversion H.
    inversion H. congruence. inversion H.
Qed.

Fixpoint dirty log :=
match log with
| TRead path result :: log' =>
  Read path (fun result' =>
    if rreq result result' then dirty log' else Exit true
  )
| TWrite path data result :: log' =>
  Read path (fun result' =>
    if wreq data result result' then dirty log' else Exit true
  )
| TExit e :: log' => Exit false
| nil => Exit false
end.

Lemma dirty_correct : forall p f f',
exit (dirty (trace p f)) f' = false -> run p f' = f'.
Proof. induction p.
- intros. simpl. simpl in H0. apply H with (f := f).
  destruct (rreq (read p f) (read p f')) eqn:Hrr.
  + apply rreq_eq in Hrr. rewrite <- Hrr. apply H0.
  + inversion H0.
- intros. simpl. simpl in H0. destruct (write p d f') eqn:Hw1, (write p d f) eqn:Hw2.
  simpl in H0. destruct (wreq d w0 (read p f')) eqn:Hwr.
  + apply wreq_correct in Hwr. inversion Hwr. rewrite Hw1 in H2. inversion H2.
    apply H with (f := f1). apply H0.
  + inversion H0.
- intros. reflexivity.
Qed.
