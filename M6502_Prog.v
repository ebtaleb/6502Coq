Definition StartIP : Z := 0.

Definition R8 : RegFile8 :=
  fun (r : Reg8) =>
    match r with
      | A => Byte.repr 0
      | X => Byte.repr 0
      | Y => Byte.repr 0
      | FLAGS => Byte.repr 0
      | STATUS => Byte.repr 0
    end.

Definition R16 :RegFile16 :=
  fun (r : Reg16) =>
    match r with
      | PC => Word.repr StartPC
    end.

Definition StartR : RegFile := (R8, R16).

Definition StartP : Program := (StartM, StartR).

Definition prog1 : list Instr :=
  (LDA_ir (Byte.repr 1)) ::
  (LDX_ir (Byte.repr 2)) ::
  (LDY_ir (Byte.repr 0)) ::
  nil.