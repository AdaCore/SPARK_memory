with Area_Math; use Area_Math;

package Memory_Analysis
with SPARK_Mode => On
is

   type Byte_Property is record
      Stack    : Boolean;
      Heap     : Boolean;
      Scrubbed : Boolean;
   end record
   with Ghost;

   type Memory_Type is array (Address_Type) of Byte_Property with Ghost;

   Memory : Memory_Type with Ghost;

   procedure Set_Heap (From, To : Address_Type)
     with
       Pre => To >= From,
       Post => (for all B in Address_Type => (if B in From .. To then Memory (B) = Memory'Old (B)'Update (Heap => True) else Memory (B) = Memory'Old (B)'Update (Heap => False))),
     Global => (In_Out => Memory);

   procedure Set_Stack (From, To : Address_Type)
     with Pre => To >= From,
       Post => (for all B in Address_Type => (if B in From .. To then Memory (B) = Memory'Old (B)'Update (Stack => True) else Memory (B) = Memory'Old (B)'Update (Stack => False))),
       Global => (In_Out => Memory);

   procedure Scrub (From, To : Address_Type)
     with Pre => To >= From,
     Post =>
       (for all B in Address_Type =>
              (if B in From .. To then Memory (B) = Memory'Old(B)'Update (Scrubbed => True)
                   else Memory (B) = Memory'Old(B))),
       Global => (In_Out => Memory);

   procedure Get_Heap_Boundaries (From, To : out Address_Type)
     with Post => (for all B in Address_Type => (Memory (B).Heap = (B in From .. To)))
     and then From <= To;

   procedure Get_Stack_Boundaries (From, To : out Address_Type)
     with Post => (for all B in Address_Type => (Memory (B).Stack = (B in From .. To)))
     and then From <= To;
--
   function Valid_Heap_And_Stack_Area
     (Heap_From, Heap_To, Stack_From, Stack_To : Address_Type) return Boolean
   is
     ((Stack_From <= Stack_To and Heap_From <= Heap_To) and then
      Heap_From not in Stack_From .. Stack_To and then
      Heap_To not in Stack_From .. Stack_To and then
      Stack_From not in Heap_From .. Heap_To and then
      Stack_To not in Heap_From .. Heap_To);

   procedure Move_Heap_And_Stack
     (Heap_From, Heap_To, Stack_From, Stack_To : Address_Type)
     with Pre => Valid_Heap_And_Stack_Area (Heap_From, Heap_To, Stack_From, Stack_To),
       Post =>
       (for all B in Address_Type =>
          (Memory (B).Scrubbed = ((Memory'Old (B).Heap or Memory'Old (B).Stack) and then not (Memory (B).Heap or Memory (B).Stack))));

end Memory_Analysis;
