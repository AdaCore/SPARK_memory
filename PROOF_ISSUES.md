# SPARK Memory Proof Issues and Fixes

This document records issues found while verifying the SPARK memory operations code with gnatprove, and the fixes applied.

## Environment

- **SPARK Pro Version**: 27.0w (20260119)
- **Provers**: Alt-Ergo 2.6.1, CVC5 1.3.2, Z3 4.15.4
- **Proof Level**: 2
- **Timeout Required**: 120 seconds for full proof

## Issues Found and Fixed

### 1. SPARK Mode Violation in memory_main.adb

**Original Issue**: The `Get_Line` function from `Ada.Text_IO` cannot be used in SPARK code because it is declared with `SPARK_Mode => Off`.

**Error**:
```
error: "Get_Line" is not allowed in SPARK (due to entity declared with SPARK_Mode Off)
```

**Fix**: Wrapped the I/O operations in a nested procedure with `SPARK_Mode => Off` and a separate declaration with a `Global` contract:

```ada
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
```

**File**: `src/memory_main.adb`

### 2. Missing Loop_Variant Annotations in area_math.adb

**Original Issue**: Several loops in the `"or"` and `"and"` operators were missing `Loop_Variant` annotations, causing "implicit aspect Always_Terminates might be incorrect" warnings.

**Fix**: Added `Loop_Variant` pragmas to all affected loops:

- Main loop in `"or"` (line 441): `pragma Loop_Variant (Decreases => (S1.Size - It1) + (S2.Size - It2));`
- Second loop in `"or"` (line 458): `pragma Loop_Variant (Decreases => S1.Size - It1);`
- Third loop in `"or"` (line 471): `pragma Loop_Variant (Decreases => S2.Size - It2);`
- Main loop in `"and"` (line 711): `pragma Loop_Variant (Decreases => (S1.Size - It1) + (S2.Size - It2));`
- Inner loop in `"and"` Combine procedure (line 580): `pragma Loop_Variant (Decreases => S2.Size - It2);`

**File**: `src/area_math.adb`

### 3. Missing Always_Terminates on Combine Procedure

**Original Issue**: The `Combine` procedure in the `"and"` function needed an `Always_Terminates` aspect.

**Fix**: Added `Always_Terminates` to the procedure specification:

```ada
procedure Combine (S1, S2 : Set; It1 : Integer; It2 : in out Integer)
  with Always_Terminates,
  Pre => ...
```

**File**: `src/area_math.adb`, line 515

### 4. Loop Variant Proof Failures

**Original Issue**: Loop variants couldn't be proven because postconditions didn't guarantee iterator increments.

**Fix #1**: Added postcondition to `Combine_And_Increment` in the `"or"` function:
```ada
and then (if not End_It1 then It1 = It1'Old + 1);
```

**Fix #2**: Added postcondition to `Combine` in the `"and"` function:
```ada
and then It2 >= It2'Old
```

**File**: `src/area_math.adb`

### 5. Assertion Helper for "and" Function

**Original Issue**: An assertion in the Combine procedure of the `"and"` function didn't prove within timeout.

**Fix**: Added intermediate assertions to help the prover:

```ada
if It2 > 1 then
   Lemma_Nothing_In_Between (S2, It2 - 1);
   pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. S2.Areas (It2).From - 1 => not Includes (B, S2));
   pragma Assert (for all B in S2.Areas (It2 - 1).To + 1 .. S1.Areas (It1).To => not Includes (B, S2));
   pragma Assert (Is_Computed (S1.Areas (It1).To));
...
```

**File**: `src/area_math.adb`, around line 686

### 6. Additional Helper Assertions for "and" Function Combine Postcondition

**Original Issue**: The postcondition `Is_Computed (S1, S2, S2.Areas (It2 - 1).To)` in the `Combine` procedure of the `"and"` function (line 556) previously required level 4 with 600s timeout.

**Root Cause**: The prover needed help understanding the monotonicity of `Is_Computed` - that if we've computed up to `S2.Areas(It2).To`, we've also computed up to `S2.Areas(It2-1).To` since the It2-1 area ends before the It2 area.

**Fix**: Added intermediate assertions at each exit point in the Combine loop to establish the `Is_Computed` monotonicity:

```ada
-- At line 659-663 (inside the "It2 = S2.Size" exit):
if It2 > 1 then
   pragma Assert (Is_Computed (S2.Areas (It2).To));
   pragma Assert (S2.Areas (It2 - 1).To < S2.Areas (It2).To);
   pragma Assert (Is_Computed (S2.Areas (It2 - 1).To));
end if;
exit;
```

**Result**: Proof now completes in under 1 second at level 2, down from 291 seconds at level 4.

**File**: `src/area_math.adb`, lines 659-663

### 7. Loop Invariant Preservation in "not" Function

**Original Issue**: Loop invariant preservation couldn't be proven for the "not" function.

**Fix**: Added an intermediate assertion before the loop invariant:

```ada
pragma Assert (for all B in 0 .. S.Areas (I).To => Includes (B, Result) /= Includes (B, S));
```

**File**: `src/area_math.adb`, line 909

### 8. Uninitialized Ghost Memory Variable

**Original Issue**: The `Memory` ghost variable in `Memory_Analysis` was not initialized, causing:
```
medium: "Memory" might not be initialized after elaboration of main program "Memory_Main"
```

**Fix**: Added default initialization:

```ada
Memory : Memory_Type := (others => (Stack => False, Heap => False, Scrubbed => False)) with Ghost;
```

**File**: `src/memory_analysis.ads`, line 16

## Remaining Warnings (Non-Critical)

The following warnings remain but do not affect proof correctness:

1. `initialization of "Old_Memory" has no effect` - memory_analysis.adb:121
2. `initialization of "Old" has no effect` - area_math.adb:172

These are ghost variables initialized for documentation purposes that the prover doesn't need.

## Proof Command

To verify all proofs pass:

```bash
gnatprove -P prj.gpr --level=2 --timeout=120 -j0
```

All 1155 checks prove successfully with no individual check taking more than 1 second.

## Summary

All 1155 checks prove successfully with SPARK Pro 27.0w at proof level 2 with a 120-second timeout. No individual check takes more than 1 second.

Only two benign warnings remain:
- `initialization of "Old_Memory" has no effect` - ghost variable in memory_analysis.adb
- `initialization of "Old" has no effect` - ghost variable in area_math.adb
