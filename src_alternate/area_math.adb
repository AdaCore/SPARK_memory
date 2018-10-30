with Ada.Text_IO; use Ada.Text_IO;
with Ada.Strings.Fixed;
with Ada.Strings; use Ada.Strings;


package body Area_Math
with SPARK_Mode => On
is
   pragma Unevaluated_Use_Of_Old (Allow);

   function Disjoint (A1, A2 : Area) return Boolean is
      (A1.To < A2.From and then A2.From - A1.To > 1);

   function Is_Consistent (Areas : Area_Array) return Boolean is
      -- REQ_1 all area are ordered, disjoint and distant by at least 1 element outide of the set
     (for all I in Areas'Range => (if I < Areas'Last then Disjoint (Areas (I), Areas (I + 1))));

   function Includes (B : Address_Type; A : Area) return Boolean
   is (B in A.From .. A.To)
     with Ghost;

   function Includes (B : Address_Type; S : Set) return Boolean
   is (for some I in 1 .. S.Size => Includes (B, S.Areas (I)));

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

   procedure Append (S : in out Set; A : Area) with
     Pre  => (S.Size = 0 or else A.From >= S.Areas (S.Size).From) and then S.Size < S.Max,
     Post => (for all B in Address_Type => Includes (B, S) = (Includes (B, S'Old) or Includes (B, A))) and then S.Size in 1 .. S.Size'Old + 1
     and then S.Areas (S.Size).From <= A.From
   is
      S_Old : constant Set := S;
   begin
      if S.Size = 0 then
         S.Areas (1) := A;
         S.Size := 1;
         pragma Assert (for all B in Address_Type => Includes (B, S) = (Includes (B, S_Old) or Includes (B, A)));
      elsif S.Areas (S.Size).To >= A.To then
         null;
         pragma Assert (for all B in Address_Type => Includes (B, S) = (Includes (B, S_Old) or Includes (B, A)));
      elsif S.Areas (S.Size).To < A.From and then A.From - S.Areas (S.Size).To > 1 then
         S.Areas (S.Size + 1) := A;
         S.Size := S.Size + 1;
         pragma Assert (for all B in Address_Type => Includes (B, S) = (Includes (B, S_Old) or Includes (B, A)));
      else
         S.Areas (S.Size).To := A.To;
         pragma Assert (for all B in Address_Type => Includes (B, S.Areas (S.Size)) = (Includes (B, S_Old.Areas (S.Size)) or Includes (B, A)));
         pragma Assert (for all B in Address_Type => Includes (B, S) = (Includes (B, S_Old) or Includes (B, A)));
      end if;
   end Append;

   -----------
   -- "or" --
   -----------

  function "or"
     (S1, S2 : Set)
      return Set
   is
      Result : Set (S1.Size + S2.Size);
      It1, It2 : Integer := 0;
   begin
      Result.Areas := (others => (others => 0));

      if S1.Size = 0 and then S2.Size = 0 then
         return Empty_Set;
      elsif S1.Size = 0 then
         return S2;
      elsif S2.Size = 0 then
         return S1;
      end if;

      loop
         pragma Loop_Invariant (It1 in 0 .. S1.Size);
         pragma Loop_Invariant (It2 in 0 .. S2.Size);
         pragma Loop_Invariant (It2 /= S2.Size or It1 /= S1.Size);
         pragma Loop_Invariant (Result.Size <= It1 + It2);
         pragma Loop_Invariant
           (Result.Size = 0 or else It1 = S1.Size or else S1.Areas (It1 + 1).From >= Result.Areas (Result.Size).From);
         pragma Loop_Invariant
           (Result.Size = 0 or else It2 = S2.Size or else S2.Areas (It2 + 1).From >= Result.Areas (Result.Size).From);
         pragma Loop_Invariant
           (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I))) or (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
         if It2 = S2.Size
           or else (It1 < S1.Size and then S1.Areas (It1 + 1).From <= S2.Areas (It2 + 1).From)
         then
            It1 := It1 + 1;
            Append (Result, S1.Areas (It1));
            pragma Assert (It1 = S1.Size or else S1.Areas (It1 + 1).From >= Result.Areas (Result.Size).From);
            pragma Assert (It2 = S2.Size or else S2.Areas (It2 + 1).From >= Result.Areas (Result.Size).From);
            pragma Assert
              (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I))) or (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
         else
            It2 := It2 + 1;
            Append (Result, S2.Areas (It2));
            pragma Assert (It1 = S1.Size or else S1.Areas (It1 + 1).From >= Result.Areas (Result.Size).From);
            pragma Assert (It2 = S2.Size or else S2.Areas (It2 + 1).From >= Result.Areas (Result.Size).From);
            pragma Assert
              (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I))) or (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
         end if;
         exit when It1 = S1.Size and then It2 = S2.Size;
      end loop;
      pragma Assert
        (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. S1.Size => Includes (B, S1.Areas (I))) or (for some I in 1 .. S2.Size => Includes (B, S2.Areas (I)))));
      return Result;
   end "or";

   procedure Lemma_Order (Areas : Area_Array) with
     Ghost,
     Pre  => Is_Consistent (Areas),
     Post => (for all I in Areas'Range =>
                (for all J in Areas'Range =>
                     (If I < J then Areas (I).To < Areas (J).From)))
   is
   begin
      null;
   end Lemma_Order;

   procedure Lemma_Nothing_Beyond_Last (Areas : Area_Array; Last : Address_Type) with
     Ghost,
     Pre  => Is_Consistent (Areas) and then (Areas'Length = 0 or else Last > Areas (Areas'Last).To),
     Post => (for all B in Address_Type => (if B >= Last then (for all I in Areas'Range => not Includes (B, Areas (I)))))
   is
   begin
      null;
   end Lemma_Nothing_Beyond_Last;

   procedure Lemma_Nothing_Before_First (Areas : Area_Array; First : Address_Type) with
     Ghost,
     Pre  => Is_Consistent (Areas) and then (Areas'Length = 0 or else First <= Areas (Areas'First).From),
     Post => (for all B in Address_Type => (if B < First then (for all I in Areas'Range => not Includes (B, Areas (I)))))
   is
   begin
      null;
   end Lemma_Nothing_Before_First;

   -----------
   -- "and" --
   -----------

  function "and"
     (S1, S2 : Set)
      return Set
   is

      procedure Lemma_And_Is_Intersection (Area1, Area2, Inter : Area) with
        Ghost,
        Pre  => (if Area1.From <= Area2.From then Inter.From = Area2.From
                   else Inter.From = Area1.From)
        and then (if Area1.To <= Area2.To then Inter.To = Area1.To
                    else Inter.To = Area2.To),
        Post =>
          (for all B in Address_Type =>
             Includes (B, Inter) =
           (Includes (B, Area1) and Includes (B, Area2)))
      is
      begin
         null;
      end Lemma_And_Is_Intersection;

      procedure Lemma_Prove_No_Last (S1, S2 : Set; It2 : Natural) with
        Pre  => S1.Size > 0 and then It2 in 1 .. S2.Size - 1 and then S1.Areas (S1.Size).To < S2.Areas (It2 + 1).From,
        Post => (for all B in Address_Type => not ((for some I in It2 + 1 .. S2.Size => Includes (B, S2.Areas (I))) and (for some I in 1 .. S1.Size => Includes (B, S1.Areas (I)))))
      is
      begin
         Lemma_Nothing_Beyond_Last (S1.Areas (1 .. S1.Size), S2.Areas (It2 + 1).From);
         Lemma_Nothing_Before_First (S2.Areas (It2 + 1 .. S2.Size), S2.Areas (It2 + 1).From);
      end Lemma_Prove_No_Last;

      Result : Set := (Max => S1.Size + S2.Size, Size => 0, Areas => (others => (others => 0)));
      It1    : Integer := 0;
      It2    : Integer := 1;
   begin

      if S1.Size = 0 or else S2.Size =  0 then
         return Empty_Set;
      end if;

      loop
         pragma Loop_Invariant (It1 in 0 .. S1.Size);
         pragma Loop_Invariant (It2 in 1 .. S2.Size);
         pragma Loop_Invariant (if It1 = 0 then It2 = 1);
         pragma Loop_Invariant (Result.Size <= It1 + It2 - 1);
         pragma Loop_Invariant
           (It2 = 1 or else S2.Areas (It2 - 1).To <= S1.Areas (It1).To);
         pragma Loop_Invariant
           (It1 <= 1 or else S1.Areas (It1 - 1).To <= S2.Areas (It2).To);
         pragma Loop_Invariant
           (Result.Size = 0
            or else S1.Areas (It1).From >= Result.Areas (Result.Size).From
            or else S2.Areas (It2).From >= Result.Areas (Result.Size).From);
         pragma Loop_Invariant
           (for all B in Address_Type =>
              Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
              and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));

         if It1 = 0 or else S1.Areas (It1).To <= S2.Areas (It2).To then
            exit when It1 = S1.Size;
            It1 := It1 + 1;
            declare
            begin
               Lemma_Order (S2.Areas (1 .. It2));
               Lemma_Nothing_Beyond_Last (S2.Areas (1 .. It2 - 1), S1.Areas (It1).From);
               pragma Assert_And_Cut
                 (for all B in Address_Type => not (Includes (B, S1.Areas (It1))
                  and (for some I in 1 .. It2 - 1 => Includes (B, S2.Areas (I)))));
            end;
         else
            exit when It2 = S2.Size;
            It2 := It2 + 1;
            declare
            begin
               Lemma_Order (S1.Areas (1 .. It1));
               Lemma_Nothing_Beyond_Last (S1.Areas (1 .. It1 - 1), S2.Areas (It2).From);
               pragma Assert_And_Cut
                 (for all B in Address_Type => not (Includes (B, S2.Areas (It2))
                  and (for some I in 1 .. It1 - 1 => Includes (B, S1.Areas (I)))));
            end;
         end if;

         if S1.Areas (It1).From <= S2.Areas (It2).From then
            if S1.Areas (It1).To < S2.Areas (It2).From then
               declare
               begin
                  Lemma_Nothing_Beyond_Last (S1.Areas (1 .. It1), S2.Areas (It2).From);
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            elsif S2.Areas (It2).To <= S1.Areas (It1).To then
               Append (Result, S2.Areas (It2));
               declare
               begin
                  Lemma_And_Is_Intersection (S2.Areas (It2), S1.Areas (It1), S2.Areas (It2));
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            else
               Append (Result, Area'(From => S2.Areas (It2).From,
                                     To   => S1.Areas (It1).To));
               declare
               begin
                  Lemma_And_Is_Intersection (S2.Areas (It2), S1.Areas (It1),
                                             Area'(From => S2.Areas (It2).From,
                                                   To   => S1.Areas (It1).To));
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            end if;
         else
            if S2.Areas (It2).To < S1.Areas (It1).From then
               declare
               begin
                  Lemma_Nothing_Beyond_Last (S2.Areas (1 .. It2), S1.Areas (It1).From);
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            elsif S1.Areas (It1).To <= S2.Areas (It2).To then
               Append (Result, S1.Areas (It1));
               declare
               begin
                  Lemma_And_Is_Intersection (S1.Areas (It1), S2.Areas (It2), S1.Areas (It1));
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            else
               Append (Result, Area'(From => S1.Areas (It1).From,
                                     To   => S2.Areas (It2).To));
               declare
               begin
                  Lemma_And_Is_Intersection (S1.Areas (It1), S2.Areas (It2),
                                             Area'(From => S1.Areas (It1).From,
                                                   To   => S2.Areas (It2).To));
                  pragma Assert_And_Cut
                    (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                     and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
               end;
            end if ;
         end if;

         pragma Assert (for all B in Address_Type => Includes (B, Result) = ((for some I in 1 .. It1 => Includes (B, S1.Areas (I)))
                        and (for some I in 1 .. It2 => Includes (B, S2.Areas (I)))));
      end loop;
      pragma Assume (Size (Result) = Result.Size);

      if It2 < S2.Size then
         Lemma_Prove_No_Last (S1, S2, It2);
      elsif It1 < S1.Size then
         Lemma_Prove_No_Last (S2, S1, It1);
      end if;

      return Result;
   end "and";

end Area_Math;
