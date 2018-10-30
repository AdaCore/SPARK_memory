with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Fixed;
with Ada.Strings; use Ada.Strings;

with Area_Math.Lemma; use Area_Math.Lemma;

package body Area_Math
with SPARK_Mode => On
is
   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Append (S : in out Set; A : Area) with
     Pre =>
       Is_Consistent (S)
       and S.Max - S.Size >= 1
       and (if S.Size > 0 then A.From >= S.Areas (S.Size).From and then A.To >= S.Areas (S.Size).To),
     Post =>
       Is_Consistent (S)
       and (if S.Size'Old = 0 then S.Size = 1
            elsif A.From > S'Old.Areas (S'Old.Size).To and then A.From - S'Old.Areas (S'Old.Size).To > 1 then S.Size - S.Size'Old = 1
            else S.Size = S.Size'Old)
       and (if A.From > Address_Type'First then
            (for all B in Address_Type'First .. A.From - 1 =>
                 Includes (B, S) = Includes (B, S'Old)))
       and (for all B in A.From .. A.To => Includes (B, S))
       and (for all B in Address_Type => (if not Includes (B, S'Old) and Includes (B, S) then B in A.From .. A.To))
       and (if A.To < Address_Type'Last then (for all B in A.To + 1 .. Address_Type'Last => not Includes (B, S)))
       and S.Areas (S.Size).From <= A.From
       and S.Areas (S.Size).To = A.To;

   procedure Append (S : in out Set; A : Area) is
      Old : constant Set := S with Ghost;
   begin
      Lemma_Order (S);

      if S.Size = 0 then
         S.Size := S.Size + 1;
         S.Areas (S.Size) := A;

         Lemma_Order (S);
         Lemma_Last_Is_Included (S);

         for I in 1 .. S.Size - 1 loop
            pragma Loop_Invariant (S.Areas (1 .. Old.Size) = Old.Areas (1 .. Old.Size));
            pragma Loop_Invariant (for all B in Address_Type'First .. S.Areas (I).To => Includes (B, S) = Includes (B, Old));
         end loop;
      elsif A.From > S.Areas (S.Size).To and then A.From - S.Areas (S.Size).To > 1 then
         S.Size := S.Size + 1;
         S.Areas (S.Size) := A;

         Lemma_Order (S);
         Lemma_Last_Is_Included (S);

         for I in 1 .. S.Size - 1 loop
            pragma Loop_Invariant (S.Areas (1 .. Old.Size) = Old.Areas (1 .. Old.Size));
            pragma Loop_Invariant (for all B in Address_Type'First .. S.Areas (I).To => Includes (B, S) = Includes (B, Old));
         end loop;
      else
         S.Areas (S.Size).To := A.To;

         Lemma_Order (S);
         Lemma_Last_Is_Included (S);

         for I in 1 .. S.Size - 1 loop
            pragma Loop_Invariant (S.Areas (1 .. Old.Size - 1) = Old.Areas (1 .. Old.Size - 1));
            pragma Loop_Invariant (for all B in Address_Type'First .. S.Areas (I).To => Includes (B, S) = Includes (B, Old));
         end loop;

         pragma Assert (S.Areas (Old.Size).From = Old.Areas (Old.Size).From);
         pragma Assert (S.Areas (Old.Size).To >= Old.Areas (Old.Size).To);
         pragma Assert (for all B in S.Areas (Old.Size).From .. Old.Areas (Old.Size).To => Includes (B, S));
         pragma Assert (for all B in S.Areas (Old.Size).From .. Old.Areas (Old.Size).To => Includes (B, Old));
         pragma Assert (for all B in S.Areas (Old.Size).From .. Old.Areas (Old.Size).To => Includes (B, S) = Includes (B, Old));
         pragma Assert (S.Size = Old.Size);
      end if;
   end Append;

   function Create (From, To : Address_Type) return Set is
   begin
      return (Max => 1, Size => 1, Areas => (1 => (From, To)));
   end Create;

   procedure Put_Line (S : Set)
     with SPARK_Mode => Off
   is
   begin
      Put ("{");

      for I in 1 .. S.Size loop
         if I > 1 then
            Put (", ");
         end if;

         Put (Ada.Strings.Fixed.Trim(S.Areas (I).From'Img, Both) & " .. " & Ada.Strings.Fixed.Trim(S.Areas(I).To'Img, Both));
      end loop;

      Put_Line ("}");
   end Put_Line;

   -----------
   -- "or" --
   -----------

  function "or"
     (S1, S2 : Set)
      return Set
   is
      Result : Set (S1.Size + S2.Size);
      It1, It2 : Integer := 1;

      function Is_Computed (S1, S2 : Set; From, To : Address_Type) return Boolean is
        (for all B in From .. To => Includes (B, Result) = ((Includes (B, S1) or Includes (B, S2))))
      with Ghost;

      function Is_Computed (S1, S2 : Set; To : Address_Type) return Boolean is
        (for all B in Address_Type'First .. To => Includes (B, Result) = ((Includes (B, S1) or Includes (B, S2))))
          with Ghost;

      procedure Lemma_One_If_Not_The_Other (S1, S2 : Set; From, To : Address_Type)
        with Pre => Is_Computed (S1, S2, From, To),
        Post => (for all B in From .. To => (if Includes (B, Result) and not Includes (B, S1) then Includes (B, S2)))
        and (for all B in From .. To => (if Includes (B, Result) and not Includes (B, S2) then Includes (B, S1))),
        Ghost
      is
      begin
         null;
      end Lemma_One_If_Not_The_Other;

      procedure Combine (S1, S2 : Set; It1 : Integer; It2 : Integer)
        with Pre =>
          -- Silver
        It1 in 1 .. S1.Size
        and then It2 in 1 .. S2.Size
        and then Natural'Last - Result.Size >= 1
        and then Result.Max - Result.Size >= 1

          -- Gold
        and then Is_Consistent (S1)
        and then Is_Consistent (S2)
        and Then Is_Consistent (Result)

          -- Platinium
        and then (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1))
        and then (if Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From)
        and then (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To))
        and then (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2))),

        Post =>
          Result.Size > 0
          and then Result.Size >= Result.Size'Old
          and then Result.Size - Result.Size'Old in 0 .. 1
          and then Is_Consistent (Result)

          -- Platinium
          and then Is_Computed (S1, S2, S1.Areas (It1).To)
          and then (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To))
          and then (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2)))
          and then (for all B in Address_Type => (if Includes (B, Result'Old) then Includes (B, Result)))
          and then Result.Areas (Result.Size).From <= S1.Areas (It1).From;

      procedure Combine (S1, S2 : Set; It1 : Integer; It2 : Integer) is
         Initial_Size : constant Natural := Result.Size with Ghost;

         function Is_Computed (From, To : Address_Type) return Boolean is
           (Is_Computed (S1, S2, From, To))
             with Ghost;

         function Is_Computed (To : Address_Type) return Boolean is
           (Is_Computed (S1, S2, To))
             with Ghost;

         Old : Set := Result with Ghost;

      begin
         Lemma_Order (S1);
         Lemma_Order (S2);
         Lemma_Order (Result);

         if Result.Size = 0 then
            -- First element, to be added unconditionally

            Append (Result, S1.Areas (It1));
            Lemma_Last_Is_Included (Result);

            pragma Assert (Is_Computed (S1, S2, S1.Areas (It1).To));
            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));
         elsif S1.Areas (It1).To <= Result.Areas (Result.Size).To then
            -- It1 is already included in Result

            pragma Assert (Is_Computed (S1, S2, S1.Areas (It1).To));
            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));
         else
            -- In all other cases, append the element (extend if needed).

            Append (Result, S1.Areas (It1));
            Lemma_Last_Is_Included (Result);
            pragma Assert (Is_Computed (S1, S2, S1.Areas (It1).To));

            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));
         end if;
      end Combine;

      function Invariant_In_Range (S1, S2 : Set; It1, It2 : Integer) return Boolean is
        (
           (It1 in 1 .. S1.Size) and then
           (It2 in 1 .. S2.Size) and then
           (Natural'Last - S1.Size - S2.Size >= 0) and then
           (Natural'Last - Result.Size >= (S1.Size - It1) + (S2.Size - It2))
        )
          with Ghost;

      function Partial_Invariant (S1, S2 : Set; It1, It2 : Integer) return Boolean is
        (
           -- Silver
           Invariant_In_Range (S1, S2, It1, It2) and then
           --(Result.Max - Result.Size > (S1.Size - It1) + (S2.Size - It2)) and then

           -- Gold
           (Is_Consistent (S1)) and then
           (Is_Consistent (S2)) and then
           (Is_Consistent (Result)) and then

           -- Partial result, if set to True then coming from one or the other input
           (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2))) and then

           (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To)) and then
           (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To)) and then

           (if S1.Areas (It1).From > Address_Type'First
            and then S1.Areas (It1).From <= S2.Areas (It2).From
            then Is_Computed (S1, S2, S1.Areas (It1).From - 1)) and then

           (if S1.Areas (It1).From <= S2.Areas (It2).From and Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From)
        )
          with Ghost;

      function Invariant (S1, S2 : Set; It1, It2 : Integer) return Boolean is
        (
           -- Silver
           Invariant_In_Range (S1, S2, It1, It2) and then
           --(Result.Max - Result.Size > (S1.Size - It1) + (S2.Size - It2)) and then

           -- Gold
           (Is_Consistent (S1)) and then
           (Is_Consistent (S2)) and then
           (Is_Consistent (Result)) and then

           -- Partial result, if set to True then coming from one or the other input
           (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2))) and then

           (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To)) and then
           (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To)) and then

           (if S1.Areas (It1).From > Address_Type'First
            and then S1.Areas (It1).From <= S2.Areas (It2).From
            then Is_Computed (S1, S2, S1.Areas (It1).From - 1)) and then

           (if S1.Areas (It1).From <= S2.Areas (It2).From and Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From) and then

           (if S2.Areas (It2).From > Address_Type'First
            and then S2.Areas (It2).From <= S1.Areas (It1).From
            then Is_Computed (S1, S2, S2.Areas (It2).From - 1)) and then

           (if S2.Areas (It2).From <= S1.Areas (It1).From and Result.Size > 0 then S2.Areas (It2).From >= Result.Areas (Result.Size).From)
        )
          with Ghost;

      function Invariant_S_Finished (S1, S2 : Set; It1, It2 : Integer) return Boolean is
        (
           Invariant_In_Range (S1, S2, It1, It2) and then
           (It1 = S1.Size) and then
           (Is_Computed (S1, S2, S1.Areas (S1.Size).To))
        )
          with Ghost;

      function Has_Result_Space_Left (S1, S2 : Set; It1, It2 : Integer; Space : Natural) return Boolean is
        (Invariant_In_Range (S1, S2, It1, It2) and then Result.Max - Result.Size - Space >= (S1.Size - It1) + (S2.Size - It2))
          with Ghost,
          Pre => Space in 1 .. 2;

      procedure Lemma_Invariant_Commutative (S1, S2 : Set; It1, It2 : Integer)
        with Pre => Invariant (S1, S2, It1, It2),
        Post => Invariant (S2, S1, It2, It1),
        Ghost
      is
      begin
         null;
      end Lemma_Invariant_Commutative;

      procedure Lemma_Partial_To_Complete_Work
        with Pre => Is_Consistent (S1) and then
        Is_Consistent (S2) and then
        Invariant_S_Finished (S1, S2, It1, It2) and then
        Invariant_S_Finished (S2, S1, It2, It1) and then
        (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2))),
        Post => Is_Computed (S1, S2, Address_Type'Last),
        Ghost
      is
      begin
         for B in Address_Type'Range loop
            Lemma_Nothing_Beyond_Last (S1);
            Lemma_Nothing_Beyond_Last (S2);
            pragma Loop_Invariant (Is_Computed (S1, S2, B));
         end loop;
      end Lemma_Partial_To_Complete_Work;

      procedure Combine_And_Increment (S1, S2 : Set; It1 : in out Integer; It2 : Integer; End_It1 : out Boolean; End_It2 : Boolean)
        with Pre => Has_Result_Space_Left (S1, S2, It1, It2, 1) and then Partial_Invariant (S1, S2, It1, It2)

        and then (if End_It2 then Invariant_S_Finished (S2, S1, It2, It1) and then (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1)))
        and then (End_It2 or else S1.Areas (It1).From <= S2.Areas (It2).From)
        and then (if Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From)
        and then (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1)),

        Post =>
          (if End_It2 then
             Invariant_S_Finished (S2, S1, It2, It1)
             and then (if Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From)
             and then (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1)))

          and then

            (if End_It1 then
               Invariant_S_Finished (S1, S2, It1, It2) and then
               (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1)) and then
               (if Has_Result_Space_Left (S1, S2, It1, It2, 2)'Old then Has_Result_Space_Left (S1, S2, It1, It2, 1))
             else (if Has_Result_Space_Left (S1, S2, It1, It2, 2)'Old then Has_Result_Space_Left (S1, S2, It1, It2, 2)
                  else Has_Result_Space_Left (S1, S2, It1, It2, 1)))

          and then

            (if    not End_It1 and not End_It2 then Invariant (S1, S2, It1, It2)
             elsif not End_It1 and     End_It2 then Partial_Invariant (S1, S2, It1, It2)
             elsif     End_It1 and not End_It2 then Partial_Invariant (S2, S1, It2, It1)
             elsif     End_It1 and     End_It2 then Partial_Invariant (S1, S2, It1, It2)) -- Then add the case if everything is done?

          and then

            (if End_It1 and not End_It2 then S2.Areas (It2).From >= Result.Areas (Result.Size).From);

      procedure Combine_And_Increment (S1, S2 : Set; It1 : in out Integer; It2 : Integer; End_It1 : out Boolean; End_It2 : Boolean) is
      begin
         Combine (S1, S2, It1, It2);
         pragma Assert (if End_It2 then Invariant_S_Finished (S2, S1, It2, It1));

         Lemma_Order (S1);
         Lemma_Order (S2);
         Lemma_Order (Result);

         if It1 = S1.Size then
            pragma Assert (if not End_It2 then S2.Areas (It2).From >= Result.Areas (Result.Size).From);

            if S2.Areas (It2).From <= S1.Areas (It1).To then
               pragma Assert (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            elsif It2 > 1 then
               Lemma_Nothing_In_Between (S2, It2 - 1);
               pragma Assert (for all B in S1.Areas (It1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S1));
               pragma Assert (Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            else
               pragma Assert (for all B in S1.Areas (It1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S1));
               pragma Assert (Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            end if;

            pragma Assert (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1));

            pragma Assert (if not End_It2 then Partial_Invariant (S2, S1, It2, It1));

            End_It1 := True;
            return;
         end if;

         End_It1 := False;

         It1 := It1 + 1;

         pragma Assert (Is_Computed (S1, S2, S1.Areas (It1 - 1).To));
         pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));

         pragma Assert (for all B in Address_Type => (if Includes (B, Result) then Includes (B, S1) or Includes (B, S2)));

         if S1.Areas (It1).From <= S2.Areas (It2).From then
            Lemma_Nothing_In_Between (S1, It1 - 1);
            pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => not Includes (B, S1));

            if It2 > 1 then
               pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => (if Includes (B, Result) then Includes (B, S2)));
               Lemma_Nothing_In_Between (S2, It2 - 1);
               pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => (if not Includes (B, Result) then not Includes (B, S2)));
               pragma Assert (Is_Computed (S1, S2, S1.Areas (It1).From - 1));
            end if;

            pragma Assert (Is_Computed (S1, S2, S1.Areas (It1).From - 1));
         else
            Lemma_Nothing_In_Between (S1, It1 - 1);
            pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => not Includes (B, S1));

            if S2.Areas (It2).From <= S1.Areas (It1 - 1).To then
               pragma Assert (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            elsif It2 > 1 then
               Lemma_Nothing_In_Between (S2, It2 - 1);
               pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S1));
               pragma Assert (Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            else
               pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S1));
               pragma Assert (Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            end if;

            pragma Assert (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1));
         end if;

         pragma Assert (if not End_It2 then Invariant (S1, S2, It1, It2) else Partial_Invariant (S1, S2, It1, It2));
      end Combine_And_Increment;

      End_It1 : Boolean := False;
      End_It2 : Boolean := False;
   begin
      Result.Size := 0;
      Result.Areas := (others => (others => 0));

      if S1.Size = 0 and then S2.Size = 0 then
         return Empty_Set;
      elsif S1.Size = 0 then
         return S2;
      elsif S2.Size = 0 then
         return S1;
      end if;

      Lemma_Order (S1);
      Lemma_Order (S2);

      pragma Assert
        (if S1.Areas (It1).From > Address_Type'First
         and then S1.Areas (It1).From <= S2.Areas (It2).From
         then Is_Computed (S1, S2, S1.Areas (It1).From - 1));

      pragma Assert
        (if S2.Areas (It2).From > Address_Type'First
         and then S2.Areas (It2).From <= S1.Areas (It1).From
         then Is_Computed (S1, S2, S2.Areas (It2).From - 1));

      loop
         pragma Loop_Invariant (Invariant (S1, S2, It1, It2));
         pragma Loop_Invariant (not End_It1 and then not End_It2);
         pragma Loop_Invariant (Has_Result_Space_Left (S1, S2, It1, It2, 2));
         pragma Loop_Invariant (Result.Size <= Result.Max);  -- BUG? Do I really need this invariant while it's an actual type predicate?

         if S1.Areas (It1).From <= S2.Areas (It2).From then
            Combine_And_Increment (S1, S2, It1, It2, End_It1, End_It2);
            exit when End_It1;
         else
            Combine_And_Increment (S2, S1, It2, It1, End_It2, End_It1);
            exit when End_It2;
            Lemma_Invariant_Commutative (S2, S1, It2, It1);
         end if;
      end loop;

      if End_It2 then
         loop
            pragma Loop_Invariant (Partial_Invariant (S1, S2, It1, It2));
            pragma Loop_Invariant (Invariant_S_Finished (S2, S1, It2, It1));
            pragma Loop_Invariant (if Result.Size > 0 then S1.Areas (It1).From >= Result.Areas (Result.Size).From);
            pragma Loop_Invariant (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1));
            pragma Loop_Invariant (Has_Result_Space_Left (S1, S2, It1, It2, 1));

            Combine_And_Increment (S1, S2, It1, It2, End_It1, End_It2);
            exit when End_It1;
         end loop;
      else
         pragma Assert (End_It1);

         loop
            pragma Loop_Invariant (Partial_Invariant (S2, S1, It2, It1));
            pragma Loop_Invariant (Invariant_S_Finished (S1, S2, It1, It2));
            pragma Loop_Invariant (if Result.Size > 0 then S2.Areas (It2).From >= Result.Areas (Result.Size).From);
            pragma Loop_Invariant (if S2.Areas (It2).From > Address_Type'First then Is_Computed (S1, S2, S2.Areas (It2).From - 1));
            pragma Loop_Invariant (Has_Result_Space_Left (S1, S2, It1, It2, 1));

            Combine_And_Increment (S2, S1, It2, It1, End_It2, End_It1);
            exit when End_It2;
         end loop;
      end if;

      Lemma_Order (S1);
      Lemma_Order (S2);
      Lemma_Order (Result);

      Lemma_Partial_To_Complete_Work;
      pragma Assert (Is_Computed (S1, S2, Address_Type'Last));

      return Result;
   end "or";

   -----------
   -- "and" --
   -----------

  function "and"
     (S1, S2 : Set)
      return Set
   is
      Result : Set (S1.Size + S2.Size);
      It1, It2 : Integer := 1;

      function Is_Computed (S1, S2 : Set; From, To : Address_Type) return Boolean is
        (for all B in From .. To => Includes (B, Result) = ((Includes (B, S1) and Includes (B, S2))))
      with Ghost;

      function Is_Computed (S1, S2 : Set; To : Address_Type) return Boolean is
        (for all B in Address_Type'First .. To => Includes (B, Result) = ((Includes (B, S1) and Includes (B, S2))))
      with Ghost;

      procedure Combine (S1, S2 : Set; It1 : Integer; It2 : in out Integer)
        with Pre =>
          -- Silver
        It1 in 1 .. S1.Size
        and then It2 in 1 .. S2.Size
        and then Natural'Last - Result.Size >= S2.Size - It2
        and then Result.Max - Result.Size > S2.Size - It2

          -- Gold
        and then Is_Consistent (S1)
        and then Is_Consistent (S2)
        and Then Is_Consistent (Result)
        and then S1.Areas (It1).From <= S2.Areas (It2).From
        and then (if Result.Size > 0 then Result.Areas (Result.Size).To <= S1.Areas (It1).To)
        and then (if Result.Size > 0 then Result.Areas (Result.Size).To <= S2.Areas (It2).To)
        and then (if Result.Size > 0 then
                    (Result.Areas (Result.Size).To < Address_Type'Last
                     and then Result.Areas (Result.Size).To + 1 < S2.Areas (It2).From))

          -- Platinium
         and then (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1, S2, S1.Areas (It1).From - 1))
         and then (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To))
         and then (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To)
         and then (if It2 = 1 then Result.Size = 0),

        Post =>
          Result.Size >= Result.Size'Old
          and then Result.Size - Result.Size'Old in It2 - It2'Old .. It2 - It2'Old + 1
          and then It2 in 1 .. S2.Size
          and then Is_Consistent (Result)
          and then (if Result.Size > 0 then Result.Areas (Result.Size).To <= S1.Areas (It1).To)
          and then (if Result.Size > 0 then Result.Areas (Result.Size).To <= S2.Areas (It2).To)

          -- Platinium
          and then Is_Computed (S1, S2, S1.Areas (It1).To)
          and then (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To))
          and then (if Result.Size > Result.Size'Old then
                      It2 > It2'Old
                      or else It2 = S2.Size
                    or else S2.Areas (It2).To > S1.Areas (It1).To) -- ADDED
          and then (It1 = S1.Size or else (if S1.Areas (It1 + 1).From <= S2.Areas (It2).From and It2 = 1 then Result.Size = 0))
          and then (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2).To)
          and then (-- There are three cases to enumerate here
                      -- case 1, It1 = S1.Size, end of the computation
                      (It1 = S1.Size) or else
                      -- case 2, the last It2 element is at least partially included, we know we're going to switch It1 and It2
                      (S1.Areas (It1 + 1).From > S2.Areas (It2).From) or else
                      -- case 3, the last It2 element is excluded, beyond the It1 point, we don't know if we're
                      -- going to switch but we can ensure the postcondition
                      (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To)
                 );

      procedure Combine (S1, S2 : Set; It1 : Integer; It2 : in out Integer) is
         Initial_Size : constant Natural := Result.Size with Ghost;

         function Is_Computed (From, To : Address_Type) return Boolean is
           (Is_Computed (S1, S2, From, To))
             with Ghost;

         function Is_Computed (To : Address_Type) return Boolean is
           (Is_Computed (S1, S2, To))
             with Ghost;

      begin
         Lemma_Order (S1);
         Lemma_Order (S2);
         Lemma_Order (Result);

         loop
            -- Silver
            pragma Loop_Invariant (Result.Max - Result.Size > S2.Size - It2);
            pragma Loop_Invariant (Result.Size - Result.Size'Loop_Entry >= 0);
            pragma Loop_Invariant (It2 <= S2.Size);
            pragma Loop_Invariant (Result.Size - Result.Size'Loop_Entry = It2 - It2'Loop_Entry);
            pragma Loop_Invariant (It2 in It2'Loop_Entry .. It2'Loop_Entry + (Result.Size - Result.Size'Loop_Entry));

            -- Gold
            pragma Loop_Invariant (Result.Size = 0 or else S2.Areas (It2).From > Address_Type'First);
            pragma Loop_Invariant (Result.Size = 0 or else Result.Areas (Result.Size).To < S2.Areas (It2).From - 1);
            pragma Loop_Invariant (Result.Size = 0 or else Result.Areas (Result.Size).To <= S1.Areas (It1).To);
            pragma Loop_Invariant (Is_Consistent (Result));

            -- Platinium
            pragma Loop_Invariant (if It2 > 1 then Is_Computed (S2.Areas (It2 - 1).To));
            pragma Loop_Invariant (if S1.Areas (It1).From > Address_Type'First then Is_Computed (S1.Areas (It1).From - 1));
            pragma Loop_Invariant (Result.Size = 0 or else (if It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To));
            pragma Loop_Invariant (if It2 = 1 then Result.Size = 0);
            pragma Loop_Invariant (It2 >= 1);
            pragma Loop_Invariant (if Result.Size > Result.Size'Loop_Entry then It2 > It2'Loop_Entry);
            pragma Loop_Invariant (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2).To);

            Lemma_Order (Result);
            Lemma_Order (S1);
            Lemma_Order (S2);

            pragma Assert (if It2 > 1 then (for all B in S2.Areas (It2 - 1).To + 1 .. Address_Type'Last => not Includes (B, Result)));

            if S2.Areas (It2).From in S1.Areas(It1).From .. S1.Areas (It1).To then
               -- there is an intersect

               -- check that everything is computed until the point of From - 1.

               if It2 > 1 then
                  pragma Assert (Is_Computed (S2.Areas (It2 - 1).To));
                  pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. Address_Type'Last => not Includes (B, Result));
                  Lemma_Nothing_In_Between (S2, It2 - 1);
                  pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S2));
                  pragma Assert (Is_Computed (S2.Areas (It2 - 1).To + 1, S2.Areas (It2).From - 1));
                  pragma Assert (Is_Computed (S2.Areas (It2).From - 1));
               elsif S2.Areas (It2).From > Address_Type'First then
                  pragma Assert (for all B in Address_Type'First .. S2.Areas (It2).From - 1 => not Includes (B, Result));
                  pragma Assert (for all B in Address_Type'First .. S2.Areas (It2).From - 1 => not Includes (B, S2));
                  pragma Assert (Is_Computed (S2.Areas (It2).From - 1));
               end if;

               if S2.Areas (It2).To in S1.Areas(It1).From .. S1.Areas(It1).To  then
                  -- The secondary region is all included in the primary one, this is a intersect

                  Append (Result, (S2.Areas (It2).From,  S2.Areas (It2).To));
                  Lemma_Last_Is_Included (Result);

                  pragma Assert (for all B in S2.Areas (It2).From .. S2.Areas (It2).To => Includes (B, Result));
                  pragma Assert (for all B in S2.Areas (It2).From .. S2.Areas (It2).To => Includes (B, S2));
                  pragma Assert (for all B in S2.Areas (It2).From .. S2.Areas (It2).To => Includes (B, S1));
                  pragma Assert (Is_Computed (S2.Areas (It2).From, S2.Areas (It2).To));

                  pragma Assert (Is_Computed (S2.Areas (It2).To));

                  if It2 = S2.Size then
                     if S2.Areas (S2.Size).To < Address_Type'Last then
                        pragma Assert (for all B in S2.Areas (It2).To + 1 .. Address_Type'Last => not Includes (B, S2));
                        pragma Assert (for all B in S2.Areas (It2).To + 1 .. Address_Type'Last => not Includes (B, Result));
                     end if;

                     pragma Assert (Is_Computed (S1.Areas (It1).To));
                     exit;
                  end if;

                  It2 := It2 + 1;

               else
                  -- Only the beginning is included

                  Append (Result, (S2.Areas (It2).From,  S1.Areas (It1).To));
                  Lemma_Last_Is_Included (Result);

                  pragma Assert (for all B in S2.Areas (It2).From .. S1.Areas (It1).To => Includes (B, Result));
                  pragma Assert (for all B in S2.Areas (It2).From .. S1.Areas (It1).To => Includes (B, S2));
                  pragma Assert (for all B in S2.Areas (It2).From .. S1.Areas (It1).To => Includes (B, S1));
                  pragma Assert (Is_Computed (S2.Areas (It2).From, S1.Areas (It1).To));

                  pragma Assert (Is_Computed (S1.Areas (It1).To));

                  pragma Assert (It1 = S1.Size or else S1.Areas (It1 + 1).From > S2.Areas (It2).From);

                  exit;
               end if;
            else
               -- there is no intersect

               pragma Assert (S2.Areas (It2).From > S1.Areas (It1).To);

               if It2 > 1 then
                  Lemma_Nothing_In_Between (S2, It2 - 1);
                  pragma Assert (Is_Computed (S1.Areas (It1).To));
               else
                  pragma Assert (Is_Computed (S1.Areas (It1).To));
               end if;

               pragma Assert (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To);

               exit;
            end if;

            Lemma_Order (Result);
         end loop;

         pragma Assert (if Result.Size > 0 then Result.Areas (Result.Size).To <= S1.Areas (It1).To);
      end Combine;

   begin
      Result.Size := 0;
      Result.Areas := (others => (others => 0));

      if S1.Size = 0 or else S2.Size =  0 then
         return Empty_Set;
      end if;

      Lemma_Order (S1);
      Lemma_Order (S2);

      pragma Assert
        (if S1.Areas (It1).From > Address_Type'First then
             (for all B in Address_Type'First .. S1.Areas (It1).From - 1 => (Includes (B, Result)) = ((Includes (B, S1) and Includes (B, S2)))));

      pragma Assert
        (if S2.Areas (It2).From > Address_Type'First then
             (for all B in Address_Type'First .. S2.Areas (It2).From - 1 => (Includes (B, Result)) = ((Includes (B, S1) and Includes (B, S2)))));

      loop
         -- Silver
         pragma Loop_Invariant (It1 in 1 .. S1.Size);
         pragma Loop_Invariant (It2 in 1 .. S2.Size);
         pragma Loop_Invariant (Natural'Last - Result.Size >= (S1.Size - It1) + (S2.Size - It2));
         pragma Loop_Invariant (Result.Max - Result.Size > (S1.Size - It1) + (S2.Size - It2));

         -- Gold
         pragma Loop_Invariant (Is_Consistent (S1));
         pragma Loop_Invariant (Is_Consistent (S2));
         pragma Loop_Invariant (Is_Consistent (Result));
         pragma Loop_Invariant (if Result.Size > 0 then Result.Areas (Result.Size).To <= S1.Areas (It1).To);
         pragma Loop_Invariant (if Result.Size > 0 then Result.Areas (Result.Size).To <= S2.Areas (It2).To);
         pragma Loop_Invariant (if Result.Size > 0 then Result.Areas (Result.Size).To < Address_Type'Last);
         pragma Loop_Invariant (if Result.Size > 0 and then It1 <= S1.Size and then It2 <= S2.Size then
                          (if S2.Areas (It2).From < S1.Areas (It1).From then Result.Areas (Result.Size).To + 1 < S1.Areas (It1).From
                           else Result.Areas (Result.Size).To + 1 < S2.Areas (It2).From));

         pragma Loop_Invariant
           (if S1.Areas (It1).From < S2.Areas (It2).From and then S1.Areas (It1).From > Address_Type'First then
                (for all B in Address_Type'First .. S1.Areas (It1).From - 1 => (Includes (B, Result)) = ((Includes (B, S1) and Includes (B, S2))))
            elsif S2.Areas (It2).From > Address_Type'First then
                (for all B in Address_Type'First .. S2.Areas (It2).From - 1 => (Includes (B, Result)) = ((Includes (B, S1) and Includes (B, S2)))));

         pragma Loop_Invariant (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To));
         pragma Loop_Invariant (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));

         pragma Loop_Invariant (if S1.Areas (It1).From <= S2.Areas (It2).From and It2 = 1 then Result.Size = 0); -- NOT NEEDED?
         pragma Loop_Invariant (if S2.Areas (It2).From <= S1.Areas (It1).From and It1 = 1 then Result.Size = 0); -- NOT NEEDED?

         pragma Loop_Invariant (if S1.Areas (It1).From <= S2.Areas (It2).From then (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To));
         pragma Loop_Invariant (if S2.Areas (It2).From <= S1.Areas (It1).From then (if Result.Size > 0 and then It1 > 1 then Result.Areas (Result.Size).To <= S1.Areas (It1 - 1).To));

         if S1.Areas (It1).From <= S2.Areas (It2).From then
            Combine (S1, S2, It1, It2);

            Lemma_Order (S1);
            Lemma_Order (S2);
            Lemma_Order (Result);

            if It1 = S1.Size then
               if S1.Areas (It1).To < Address_Type'Last then
                  pragma Assert (if Result.Size > 0 then Result.Areas (Result.Size).To <= S1.Areas (It1).To);
                  pragma Assert (if Result.Size > 0 then Result.Areas (Result.Size).To <= S2.Areas (It2).To);

                  pragma Assert (for all B in S1.Areas (It1).To + 1 .. Address_Type'Last => not Includes (B, S1));
                  Lemma_Nothing_Beyond_Last (Result);
                  pragma Assert (for all B in S1.Areas (It1).To + 1 .. Address_Type'Last => not Includes (B, Result));
                  pragma Assert (for all B in S1.Areas (It1).To + 1 .. Address_Type'Last => Includes (B, Result) = (Includes (B, S1) and Includes (B, S2)));
               end if;

               pragma Assert (for all B in Address_Type'First .. S1.Areas (S1.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));
               pragma Assert (for all B in Address_Type'First .. S2.Areas (S2.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));

               exit;
            end if;

            It1 := It1 + 1;

            Lemma_Nothing_In_Between (S1, It1 - 1);
            pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => not Includes (B, S1));
            Lemma_Nothing_Beyond_Last (Result);
            pragma Assert (for all B in S1.Areas (It1 - 1).To + 1 .. S1.Areas (It1).From - 1 => not Includes (B, Result));
            pragma Assert (for all B in Address_Type'First .. S1.Areas (It1).From - 1 => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));

            pragma Assert (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To));
            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));

            -- START TRY
            pragma Assert (if S1.Areas (It1).From <= S2.Areas (It2).From then (if Result.Size > 0 and then It2 > 1 then Result.Areas (Result.Size).To <= S2.Areas (It2 - 1).To));
            pragma Assert (if S2.Areas (It2).From <= S1.Areas (It1).From then (if Result.Size > 0 and then It1 > 1 then Result.Areas (Result.Size).To <= S1.Areas (It1 - 1).To));
            -- END TRY
         else
            Combine (S2, S1, It2, It1);

            Lemma_Order (S1);
            Lemma_Order (S2);
            Lemma_Order (Result);

            pragma Assert (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To));
            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));

            if It2 = S2.Size then

               if S2.Areas (It2).To < Address_Type'Last then
                  pragma Assert (for all B in S2.Areas (It2).To + 1 .. Address_Type'Last => not Includes (B, S2));
                  pragma Assert (for all B in S2.Areas (It2).To + 1 .. Address_Type'Last => not Includes (B, Result));
                  pragma Assert (for all B in S2.Areas (It2).To + 1 .. Address_Type'Last => Includes (B, Result) = (Includes (B, S1) and Includes (B, S2)));
               end if;

               pragma Assert (for all B in Address_Type'First .. S1.Areas (S1.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));
               pragma Assert (for all B in Address_Type'First .. S2.Areas (S2.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));

               exit;
            end if;

            It2 := It2 + 1;

            Lemma_Nothing_In_Between (S2, It2 - 1);
            pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S2));
            Lemma_Nothing_Beyond_Last (Result);
            pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, Result));
            pragma Assert (for all B in Address_Type'First .. S2.Areas (It2).From - 1 => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));

            pragma Assert (if It1 > 1 then Is_Computed (S1, S2, S1.Areas (It1 - 1).To));
            pragma Assert (if It2 > 1 then Is_Computed (S1, S2, S2.Areas (It2 - 1).To));
         end if;
      end loop;

      Lemma_Order (S1);
      Lemma_Order (S2);
      Lemma_Order (Result);

      pragma Assert (for all B in Address_Type'First .. S1.Areas (S1.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));
      pragma Assert (for all B in Address_Type'First .. S2.Areas (S2.Areas'Last).To => (Includes (B, Result)) = (Includes (B, S1) and Includes (B, S2)));

      pragma Assert (for all B in Address_Type => (Includes (B, Result)) = ((Includes (B, S1) and Includes (B, S2))));

      return Result;
   end "and";

   -----------
   -- "not" --
   -----------

   function "not" (S : Set) return Set
   is
      Result : Set (S.Size + 1);
   begin
      if S.Size = 0 then
         Lemma_Last_Is_Included (Full_Set);
         pragma Assert (for all B in 0 .. Address_Type'Last => not Includes (B, S));
         pragma Assert (for all B in 0 .. Address_Type'Last => Includes (B, Full_Set));
         pragma Assert (for all B in 0 .. Address_Type'Last => Includes (B, Full_Set) /= Includes (B, S));
         return Full_Set;
      end if;

      Result.Size := 0;
      Result.Areas := (others => (others => 0));

      Lemma_Order (S);

      if S.Areas (1).From /= Address_Type'First then
         Result.Size := Result.Size + 1;
         Result.Areas (Result.Size) := (Address_Type'First, S.Areas (1).From - 1);

         Lemma_Order (Result);
         Lemma_Last_Is_Included (Result);

         pragma Assert (for all B in Result.Areas (Result.Size).From .. Result.Areas (Result.Size).To => Includes (B, Result));
         pragma Assert (for all B in Result.Areas (Result.Size).From .. Result.Areas (Result.Size).To => not Includes (B, S));

         pragma Assert (for all B in Result.Areas (Result.Size).To + 1.. S.Areas (1).To => not Includes (B, Result));
         pragma Assert (for all B in Result.Areas (Result.Size).To + 1 .. S.Areas (1).To => Includes (B, S));

         pragma Assert (for all B in 0 .. S.Areas (1).To => Includes (B, Result) /= Includes (B, S));
      end if;

      pragma Assert (Is_Consistent (Result));

      Lemma_Order (Result);

      pragma Assert (for all B in 0 .. S.Areas (1).To => Includes (B, Result) /= Includes (B, S));

      for I in 1 .. S.Size - 1 loop
         Lemma_Order (S);
         Lemma_Order (Result);

         Result.Size := Result.Size + 1;
         Result.Areas (Result.Size) := (S.Areas (I).To + 1, S.Areas (I + 1).From - 1);

         Lemma_Order (Result);
         Lemma_Last_Is_Included (Result);
         Lemma_Nothing_In_Between (S, I);

         -- Assertions needed for platinium
         pragma Assert (for all B in Result.Areas (Result.Size).From .. Result.Areas (Result.Size).To => Includes (B, Result));
         pragma Assert (for all B in Result.Areas (Result.Size).From .. Result.Areas (Result.Size).To => not Includes (B, S));

         pragma Assert (for all B in Result.Areas (Result.Size).To + 1.. S.Areas (I + 1).To => not Includes (B, Result));
         pragma Assert (for all B in Result.Areas (Result.Size).To + 1 .. S.Areas (I + 1).To => Includes (B, S));

         pragma Assert (for all B in Result.Areas (Result.Size).From.. S.Areas (I + 1).To => Includes (B, Result) /= Includes (B, S));

         -- Silver, no RTE
         pragma Loop_Invariant (Result.Size <= I + 1);

         -- Gold, Is_Consistent
         pragma Loop_Invariant (Result.Size in Result.Areas'Range);
         pragma Loop_Invariant (Result.Areas (Result.Size).To < S.Areas (I + 1).From);
         pragma Loop_Invariant (Is_Consistent (S));
         pragma Loop_Invariant (Is_Consistent (Result));

         -- Platinium, S = not E
         pragma Loop_Invariant (for all B in 0 .. S.Areas (I + 1).To  => Includes (B, Result) /= Includes (B, S));
      end loop;

      -- Gold

      Lemma_Order (Result);
      Lemma_Order (S);

      -- Platinium
      pragma Assert (for all B in 0 .. S.Areas (S.Size).To  => Includes (B, Result) /= Includes (B, S));

      if S.Areas (S.Size).To /= Address_Type'Last then
         pragma Assert (if S.Size > 1 then Result.Areas (Result.Size).To < S.Areas (S.Size).From);

         Result.Size := Result.Size + 1;
         Result.Areas (Result.Size) := (S.Areas (S.Size).To + 1, Address_Type'Last);
         Lemma_Order (Result);
         Lemma_Last_Is_Included (Result);

         -- Gold
         pragma Assert (Is_Consistent (Result));

         -- Platinium

         -- The prover needs a bit of help believing that the previous areas have not been touched
         pragma Assert (if S.Size > 1 then (for all B in 0 .. S.Areas (S.Size).To => Includes (B, Result) /= Includes (B, S))); -- ???
         pragma Assert (if S.Size = 1 then (for all B in 0 .. S.Areas (S.Size).To => Includes (B, Result) /= Includes (B, S)));

         pragma Assert (for all B in Result.Areas (Result.Size).From .. Address_Type'Last => Includes (B, Result));
         pragma Assert (for all B in Result.Areas (Result.Size).From .. Address_Type'Last => not Includes (B, S));

         pragma Assert (for all B in Result.Areas (Result.Size).From .. Address_Type'Last => Includes (B, Result) /= Includes (B, S));
         pragma Assert (for all B in 0 .. S.Areas (S.Size).To => Includes (B, Result) /= Includes (B, S));

         pragma Assert (for all B in 0 .. Address_Type'Last => Includes (B, Result) /= Includes (B, S));
      end if;

      pragma Assert (Is_Consistent (Result));

      pragma Assert (for all B in 0 .. Address_Type'Last => Includes (B, Result) /= Includes (B, S));

      return Result;
   end "not";

end Area_Math;
