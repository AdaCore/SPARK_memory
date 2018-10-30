package Area_Math
  with SPARK_Mode => On
is

   Word_Size    : constant := 32;
   Memory_Size  : constant := 2 ** Word_Size;
   type Address_Type_Base is mod Memory_Size;
   type Address_Type is new Address_Type_Base;

   function "+" (Left, Right : Address_Type) return Address_Type
   is (Address_Type (Address_Type_Base (Left) + Address_Type_Base (Right)))
     with Pre => Address_Type_Base'Last - Address_Type_Base (Left) >= Address_Type_Base (Right);

   function "-" (Left, Right : Address_Type) return Address_Type
   is (Address_Type (Address_Type_Base (Left) - Address_Type_Base (Right)))
     with Pre => Left >= Right;

   type Area is record
      From, To : Address_Type;
   end record
     with Predicate => From <= To;

   type Area_Array is array (Natural range <>) of Area;

   type Set (Max : Natural) is record
      Size  : Natural;
      Areas : Area_Array (1 .. Max);
   end record
     with Predicate => Set.Size <= Max;

   Empty_Set : constant Set := (Max => 0, Size => 0, Areas => (others => (0, 0)));
   Full_Set : constant Set := (Max => 1, Size => 1, Areas => (others => (Address_Type'First, Address_Type'Last)));

   function Is_Consistent (S : Set) return Boolean is
     ((for all I in 1 .. S.Size - 1 => S.Areas (I).To < S.Areas (I + 1).From and then S.Areas (I + 1).From - S.Areas (I).To > 1));

   function Create (From, To : Address_Type) return Set
     with Pre => From <= To,
     Post => Create'Result.Max = 1
     and then Create'Result.Size = 1
     and then (for all B in Address_Type => Includes (B, Create'Result) = (B in From .. To));

   procedure Put_Line (S : Set);

   function Includes (B : Address_Type; S : Set) return Boolean
   is (for some I in 1 .. S.Size => B in S.Areas (I).From .. S.Areas (I).To)
     with Ghost;

   function "or" (S1, S2 : Set) return Set
     with Pre =>
        Is_Consistent (S1) and
        Is_Consistent (S2) and
        Positive'Last - S1.Size - S2.Size >= 0,
     Post => "or"'Result.Size <= S1.Size + S2.Size
     and Is_Consistent ("or"'Result)
     and (for all B in Address_Type => (Includes (B, "or"'Result)) = ((Includes (B, S1) or Includes (B, S2))));

   function "and" (S1, S2 : Set) return Set
     with Pre =>
        Is_Consistent (S1) and
        Is_Consistent (S2) and
        Positive'Last - S1.Size - S2.Size >= 0,
     Post => "and"'Result.Size <= S1.Size + S2.Size
     and Is_Consistent ("and"'Result)
     and (for all B in Address_Type => (Includes (B, "and"'Result)) = ((Includes (B, S1) and Includes (B, S2))));

   function "not" (S : Set) return Set
     with Pre =>
       Positive'Last - S.Size > 0
         and Is_Consistent (S),
     Post =>
       Is_Consistent ("not"'Result) and then
       (for all B in Address_Type => Includes (B, S) /= Includes (B, "not"'Result)) and then
       "not"'Result.Size <= S.Size + 1 and then
       "not"'Result.Max <= S.Size + 1;

end Area_Math;
