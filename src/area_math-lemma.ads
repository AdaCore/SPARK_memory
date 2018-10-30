package Area_Math.Lemma
with SPARK_Mode
is
   -- Lemma are used for two purposes:
   --   Manually demonstrating an implication between two truths (a Pre and a Post)
   --   Reducing the scope of hypothesis need to automatically run such demonstration
   --      (Lemma will only consider the pre and predicates).

   procedure Lemma_Order (S : Set) with
     Ghost,
     Pre => (for all I in 1 .. S.Size - 1 => S.Areas (I).To < S.Areas (I + 1).From),
     Post =>
       (for all I in 1 .. S.Size - 1 => (for all J in I + 1 .. S.Size => S.Areas (I).To < S.Areas (J).From));

   procedure Lemma_Last_Is_Included (S : Set) with
     Ghost,
     Pre => Is_Consistent (S),
     Post => S.Size = 0 or else (for all B in S.Areas (S.Size).From .. S.Areas (S.Size).To => Includes (B, S));

   procedure Lemma_Nothing_In_Between (S : Set; Left : Natural) with
     Ghost,
     Pre =>
       Is_Consistent (S) and
       Left in 1 .. S.Size - 1,
     Post => (for all B in S.Areas (Left).To + 1 .. S.Areas (Left + 1).From - 1 => not Includes (B, S));

   procedure Lemma_Nothing_Before_First (S : Set) with
     Ghost,
     Pre => Is_Consistent (S),
     Post => (if S.Size = 0 then (for all B in Address_Type => not Includes (B, S))
                elsif S.Areas (1).From > Address_Type'First then
                  (for all B in Address_Type'First .. S.Areas (1).From - 1 => not Includes (B, S)));


   procedure Lemma_Nothing_Beyond_Last (S : Set) with
     Ghost,
     Pre => Is_Consistent (S),
     Post => (if S.Size = 0 then (for all B in Address_Type => not Includes (B, S))
                elsif S.Areas (S.Size).To < Address_Type'Last then
                  (for all B in S.Areas (S.Size).To + 1 .. Address_Type'Last => not Includes (B, S)));

end Area_Math.Lemma;
