with Interfaces.C; use Interfaces.C;

with Area_Math.Lemma; use Area_Math.Lemma;

package body Memory_Analysis
with SPARK_Mode => On
is

   --------------
   -- Set_Heap --
   --------------

   procedure Set_Heap
     (From, To : Address_Type)
     with SPARK_Mode => Off
   is
      FromHeap : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromHeap";

      ToHeap : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromHeap";
   begin
      FromHeap := Interfaces.C.unsigned (From);
      ToHeap := Interfaces.C.unsigned (From);
   end Set_Heap;

   ---------------
   -- Set_Stack --
   ---------------

   procedure Set_Stack
     (From, To : Address_Type)
     with SPARK_Mode => Off
   is
      FromStack : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromStack";

      ToStack : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "toStack";
   begin
      FromStack := Interfaces.C.unsigned (From);
      ToStack := Interfaces.C.unsigned (From);
   end Set_Stack;

   -----------
   -- Scrub --
   -----------

   procedure Scrub
     (From, To : Address_Type)
     with SPARK_Mode => Off
   is
   begin
      -- TODO: This is not implemented in the context of this example
      null;
   end Scrub;

   -------------------------
   -- Get_Heap_Boundaries --
   -------------------------

   procedure Get_Heap_Boundaries
     (From, To : out Address_Type)
     with SPARK_Mode => Off
   is
      FromHeap : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromHeap";

      ToHeap : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromHeap";
   begin
      From := Address_Type (FromHeap);
      To := Address_Type (ToHeap);
   end Get_Heap_Boundaries;

   --------------------------
   -- Get_Stack_Boundaries --
   --------------------------

   procedure Get_Stack_Boundaries
     (From, To : out Address_Type)
     with SPARK_Mode => Off
   is
      FromStack : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromStack";

      ToStack : Interfaces.C.unsigned
        with Import,
        Convention => C,
        External_Name => "fromStack";
   begin
      From := Address_Type (FromStack);
      To := Address_Type (ToStack);
   end Get_Stack_Boundaries;

   -------------------------
   -- Move_Heap_And_Stack --
   -------------------------

   procedure Reset_Scrub
     with Post =>
       (for all B in Address_Type'Range =>
          Memory (B) = Memory'Old(B)'Update (Scrubbed => False)),
     Ghost;

   procedure Reset_Scrub is
      Old_Memory : Memory_Type := Memory;
   begin
      for B in Address_Type'Range loop
         Memory (B).Scrubbed := False;

         pragma Loop_Invariant
           (for all B2 in Address_Type'First .. B =>
              Memory (B2) = Memory'Loop_Entry(B2)'Update (Scrubbed => False));
      end loop;
   end Reset_Scrub;


   procedure Lemma_No_Overlap (Heap_From, Heap_To, Stack_From, Stack_To : Address_Type)
     with Pre => Valid_Heap_And_Stack_Area (Heap_From, Heap_To, Stack_From, Stack_To),
     Post => (for all B in Heap_From .. Heap_To => B not in Stack_From .. Stack_To)
     and (for all B in Stack_From .. Stack_To => B not in Heap_From .. Heap_To),
       Ghost
   is
   begin
      null;
   end Lemma_No_Overlap;

   procedure Move_Heap_And_Stack
     (Heap_From, Heap_To, Stack_From, Stack_To : Address_Type)
   is
      Prev_Heap_From, Prev_Heap_To, Prev_Stack_From, Prev_Stack_To : Address_Type;
   begin
      Get_Stack_Boundaries (Prev_Stack_From, Prev_Stack_To);
      Get_Heap_Boundaries (Prev_Heap_From, Prev_Heap_To);

      Reset_Scrub;

      declare
         Prev : Set := Create (Prev_Heap_From, Prev_Heap_To) or Create (Prev_Stack_From, Prev_Stack_To);
         Next : Set := Create (Heap_From, Heap_To) or Create (Stack_From, Stack_To);
         To_Scrub : Set := Prev and not Next;
      begin
         Lemma_Nothing_Beyond_Last (To_Scrub);

         for I in 1 .. To_Scrub.Size loop
            Scrub (To_Scrub.Areas (I).From, To_Scrub.Areas (I).To);

            if I = 1 then
               Lemma_Nothing_Before_First (To_Scrub);
            else
               Lemma_Nothing_In_Between (To_Scrub, I - 1);
            end if;

            pragma Loop_Invariant
              (if To_Scrub.Areas (I).To < Address_Type'Last then
                    (for all B in To_Scrub.Areas (I).To + 1 .. Address_Type'Last => not Memory (B).Scrubbed));
            pragma Loop_Invariant
              (for all B in Address_Type'First .. To_Scrub.Areas (I).To => Includes (B, To_Scrub) = Memory (B).Scrubbed);
         end loop;

         Lemma_Nothing_Beyond_Last (To_Scrub);
         Lemma_No_Overlap (Heap_From, Heap_To, Stack_From, Stack_To);

         Set_Stack (Stack_From, Stack_To);
         Set_Heap (Heap_From, Heap_To);
      end;
   end Move_Heap_And_Stack;

end Memory_Analysis;

