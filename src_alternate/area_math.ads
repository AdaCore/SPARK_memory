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

   type Set (Max : Natural) is private;

   Empty_Set : constant Set;
   Full_Set  : constant Set;

   function Includes (B : Address_Type; S : Set) return Boolean with Ghost;

   function Size (S : Set) return Natural with Ghost;

   function Create (From, To : Address_Type) return Set
     with Pre => From <= To,
     Post => Create'Result.Max = 1
     and then Size (Create'Result) = 1
     and then (for all B in Address_Type => Includes (B, Create'Result) = (B in From .. To));

   procedure Put_Line (S : Set);

   function "or" (S1, S2 : Set) return Set
     with Pre =>
        Positive'Last - Size (S1) - Size (S2) >= 0,
     Post => Size ("or"'Result) <= Size (S1) + Size (S2)
     and (for all B in Address_Type => (Includes (B, "or"'Result)) = ((Includes (B, S1) or Includes (B, S2))));

   function "and" (S1, S2 : Set) return Set
     with Pre =>
        Positive'Last - Size (S1) - Size (S2) >= 0,
     Post => Size ("and"'Result) <= Size (S1) + Size (S2)
     and (for all B in Address_Type => (Includes (B, "and"'Result)) = ((Includes (B, S1) and Includes (B, S2))));
--
--     function "not" (S : Set) return Set
--       with Pre =>
--         Positive'Last - S.Size > 0
--           and Is_Consistent (S),
--       Post =>
--         Is_Consistent ("not"'Result) and then
--         (for all B in Address_Type => Includes (B, S) /= Includes (B, "not"'Result)) and then
--         "not"'Result.Size <= S.Size + 1 and then
--         "not"'Result.Max <= S.Size + 1;
private

   type Area is record
      From, To : Address_Type;
   end record
     with Predicate => From <= To;
     -- REQ_2 From and To are ordered, there is no empty range

   type Area_Array is array (Natural range <>) of Area;

   function Is_Consistent (Areas : Area_Array) return Boolean;

   type Set (Max : Natural) is record
      Size  : Natural := 0;
      Areas : Area_Array (1 .. Max);
   end record
     with Predicate => Set.Size <= Max
     and then Is_Consistent (Set.Areas (1 .. Set.Size));

   Empty_Set : constant Set := (Max => 0, Size => 0, Areas => (others => (0, 0)));
   Full_Set : constant Set := (Max => 1, Size => 1, Areas => (others => (Address_Type'First, Address_Type'Last)));

   function Size (S : Set) return Natural is (S.Size);

end Area_Math;
