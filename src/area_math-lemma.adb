package body Area_Math.Lemma
with SPARK_Mode
is

   procedure Lemma_Order
     (S : Set)
   is
   begin
      if S.Size = 0 then
         return;
      end if;

      for I in 1 .. S.Size - 1 loop
         for J in I + 1 .. S.Size loop
            pragma Assert (S.Areas (J - 1).To < S.Areas (J).From);
            pragma Loop_Invariant (for all R in I + 1 .. J => S.Areas (I).To < S.Areas (R).From);
         end loop;

         pragma Loop_Invariant
           ((for all R in 1 .. I => (for all T in R + 1 .. S.Size => S.Areas (R).To < S.Areas (T).From)));
      end loop;
   end Lemma_Order;

   procedure Lemma_Last_Is_Included (S : Set)
   is
   begin
      null;
   end Lemma_Last_Is_Included;

   procedure Lemma_Nothing_In_Between (S : Set; Left : Natural) is
   begin
      Lemma_Order (S);

      for K in 1 .. S.Size loop
         pragma Loop_Invariant (for all B in S.Areas (Left).To + 1 .. S.Areas (Left + 1).From - 1 =>
                                   not (for some I in 1 .. K => B in S.Areas (I).From .. S.Areas (I).To));
      end loop;
   end Lemma_Nothing_In_Between;

   procedure Lemma_Nothing_Before_First (S : Set) is
   begin
      Lemma_Order (S);
   end Lemma_Nothing_Before_First;

   procedure Lemma_Nothing_Beyond_Last (S : Set) is
   begin
      Lemma_Order (S);
   end Lemma_Nothing_Beyond_Last;

end Area_Math.Lemma;
