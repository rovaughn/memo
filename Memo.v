Require Export Map.
Require Export List.


Definition Component := nat.
Definition Path := list Component.
Definition Data := nat.
Definition ExitStatus := nat.

Inductive Files :=
| Dir : Map Component Files -> Files
| File : Data -> Files
.

Inductive ReadResult :=
| ReadIsDir : ReadResult
| ReadNoEnt : ReadResult
| ReadNotDir : ReadResult
| ReadSuccess : Data -> ReadResult
.

Inductive WriteResult :=
| WriteIsDir : WriteResult
| WriteNoEnt : WriteResult
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
  | None => ReadNoEnt
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
    | _   => (WriteNoEnt, files)
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

Inductive Action :=
| Read : Path -> (ReadResult -> Action) -> Action
| Write : Path -> Data -> (WriteResult -> Action) -> Action
| Exit : ExitStatus -> Action
.

Inductive Trace :=
| TRead : Path -> ReadResult -> Trace
| TWrite : Path -> Data -> WriteResult -> Trace
| TExit : ExitStatus -> Trace
.

Fixpoint and_then a b :=
match a with
| Read path next => Read path (fun rr => and_then (next rr) b)
| Write path data next => Write path data (fun rr => and_then (next rr) b)
| Exit n =>
  match n with
  | 0 => b
  | n => Exit n
  end
end.

Fixpoint or_else a b :=
match a with
| Read path next => Read path (fun rr => or_else (next rr) b)
| Write path data next => Write path data (fun rr => or_else (next rr) b)
| Exit n =>
  match n with
  | 0 => Exit 0
  | n => b
  end
end.

Fixpoint trace action files: list Trace :=
match action with
| Read path next =>
  let rr := read path files
  in TRead path rr :: trace (next rr) files
| Write path data next =>
  let (wr, files') := write path data files
  in TWrite path data wr :: trace (next wr) files'
| Exit n => TExit n :: nil
end.

Fixpoint run action files: Files :=
match action with
| Read path next => run (next (read path files)) files
| Write path data next =>
  let (wr, files') := write path data files
  in run (next wr) files'
| Exit n => files
end.

Definition cp from to := Read from (fun rr => match rr with
| ReadIsDir => Exit 1
| ReadNotDir => Exit 2
| ReadNoEnt => Exit 3
| ReadSuccess data => Write to data (fun wr => match wr with
  | WriteIsDir => Exit 4
  | WriteNotDir => Exit 5
  | WriteNoEnt => Exit 6
  | WriteSuccess => Exit 0
  end)
end
).

Definition ex: Action := and_then (cp (1::nil) (2::nil)) (cp (3::nil) (4::nil)).

Compute (run ex exfs).
Compute (trace ex exfs).
Definition action_eq a a' := forall f, run a f = run a' f.

Notation "A ~ B" := (action_eq A B) (at level 86).

Lemma action_eq_refl: forall a, a ~ a.
Proof. unfold action_eq. induction a.
- simpl. intros. apply H.
- simpl. intros. destruct (write p d f). apply H.
- simpl. tauto.
Qed.

Lemma action_eq_run: forall a b,
a ~ b <-> forall f, run a f = run b f.
Proof. split.
- intros. apply H.
- intros. unfold action_eq. apply H.
Qed.

Lemma action_eq_trans: forall a b c,
a ~ b -> b ~ c -> a ~ c.
Proof.
intros. unfold action_eq in H. unfold action_eq in H0. unfold action_eq.
intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma action_eq_comm: forall a b,
a ~ b -> b ~ a.
Proof.
intros. unfold action_eq. unfold action_eq in H.
intros. symmetry. apply H.
Qed.

Definition trivial_memo (log : list Trace) (action : Action): Action := action.

Lemma trivial_memo_correct : forall a w, trivial_memo (trace a w) a ~ a.
Proof. unfold action_eq. unfold trivial_memo. tauto. Qed.

Definition rreq r1 r2 :=
match r1, r2 with
| ReadIsDir, ReadIsDir => true
| ReadNoEnt, ReadNoEnt => true
| ReadNotDir, ReadNotDir => true
| ReadSuccess d1, ReadSuccess d2 => Nat.eqb d1 d2
| _, _ => false
end.

Lemma rreq_eq: forall r1 r2, rreq r1 r2 = true <-> r1 = r2.
Proof. split.
- destruct r1, r2.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. inversion H. intros. inversion H. intros. inversion H. intros. inversion H.
  auto. intros. simpl in H. apply PeanoNat.Nat.eqb_eq in H. rewrite H. reflexivity.
- intros. rewrite H. destruct r2.
  auto. auto. auto. simpl. apply PeanoNat.Nat.eqb_refl.
Qed.

Fixpoint r_memo log action :=
match log with
| TRead path result :: log' =>
  Read path (fun result' =>
    if rreq result result'
    then r_memo log' action
    else action
  )
| _ => action
end.

Lemma r_memo_fold_read: forall log a p f f',
run (r_memo (trace log f) (Read p a)) f' =
run (r_memo (trace log f) (a (read p f'))) f'.
Proof. induction log.
- intros. simpl. destruct (rreq (read p f) (read p f')).
  + apply H.
  + reflexivity.
- intros. simpl. destruct (write p d f). reflexivity.
- intros. reflexivity.
Qed.

Lemma r_memo_correct: forall a f, r_memo (trace a f) a ~ a.
Proof. induction a.
- simpl. unfold action_eq. intros f f'.
  simpl. destruct (rreq (read p f) (read p f')) eqn:Heq.
  + apply rreq_eq in Heq. rewrite r_memo_fold_read.
    rewrite <- Heq.
    clear Heq. generalize dependent f'. rewrite <- action_eq_run.
    pose (H (read p f)). apply a0.
  + reflexivity.
- intros. simpl. destruct (write p d f). simpl. apply action_eq_refl.
- intros. simpl. apply action_eq_refl.
Qed.

Definition wreq d w r: bool :=
match w, r with
| WriteIsDir, ReadIsDir => true
| WriteNoEnt, ReadNoEnt => true
| WriteNotDir, ReadNotDir => true
| WriteSuccess, ReadSuccess d' => Nat.eqb d d'
| _, _ => false
end.


