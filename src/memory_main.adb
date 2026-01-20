with Ada.Text_IO; use Ada.Text_IO;
with Memory_Analysis; use Memory_Analysis;
with Area_Math; use Area_Math;

procedure Memory_Main
  with SPARK_Mode => On
is
   Heap_Start, Heap_End : Address_Type;
   Stack_Start, Stack_End : Address_Type;

   procedure Read_Input
     with Global => (Output => (Heap_Start, Heap_End, Stack_Start, Stack_End));

   procedure Read_Input
     with SPARK_Mode => Off
   is
   begin
      Stack_Start := Address_Type'Value (Get_Line);
      Stack_End := Address_Type'Value (Get_Line);
      Heap_Start := Address_Type'Value (Get_Line);
      Heap_End := Address_Type'Value (Get_Line);
   end Read_Input;

begin
   Set_Heap (16#00A0_0000#, 16#00AF_FFFF#);
   Set_Stack (16#00B0_0000#, 16#00BF_FFFF#);

   Read_Input;

   if not Valid_Heap_And_Stack_Area (Stack_Start, Stack_End, Heap_Start, Heap_End) then
      return;
   end if;

   Move_Heap_And_Stack (Stack_Start, Stack_End, Heap_Start, Heap_End);
end Memory_Main;


