#!/bin/bash
# Script to benchmark individual Mathlib files with and without kernel typechecking

set -e

# Parse build order from the verbose build log
echo "Extracting build order..."
grep "Built Mathlib\." build_verbose.log | \
  sed -E 's/.*Built (Mathlib[^ ]+).*/\1/' > mathlib_build_order.txt

echo "Found $(wc -l < mathlib_build_order.txt) Mathlib modules"

# Backup the original lakefile
cp lakefile.lean lakefile.lean.backup

# Create output directory for results
mkdir -p benchmark_results

echo "============================================"
echo "PHASE 1: Building with normal settings"
echo "============================================"

# Clean and build each file with normal settings
lake clean

while IFS= read -r module; do
  file_path=$(echo "$module" | sed 's/\./\//g').lean
  echo "[$module] Building normally..."

  # Capture both time and check for errors
  { time lake build "$file_path" 2>&1; } 2>&1 | tee "benchmark_results/${module}.normal.log"

done < mathlib_build_order.txt

echo ""
echo "============================================"
echo "PHASE 2: Modifying lakefile for skipKernelTC"
echo "============================================"

# Modify lakefile to add debug.skipKernelTC option
# Insert it after the autoImplicit line
sed -i '/⟨`autoImplicit, false⟩,/a\    ⟨`debug.skipKernelTC, true⟩,' lakefile.lean

echo "Modified lakefile.lean to enable debug.skipKernelTC"
grep -A2 -B2 "debug.skipKernelTC" lakefile.lean

echo ""
echo "============================================"
echo "PHASE 3: Building with skipKernelTC=true"
echo "============================================"

# Clean and build each file with skipKernelTC
lake clean

while IFS= read -r module; do
  file_path=$(echo "$module" | sed 's/\./\//g').lean
  echo "[$module] Building with skipKernelTC..."

  # Capture both time and check for errors
  { time lake build "$file_path" 2>&1; } 2>&1 | tee "benchmark_results/${module}.skipkernel.log"

done < mathlib_build_order.txt

echo ""
echo "============================================"
echo "PHASE 4: Restoring lakefile"
echo "============================================"

# Restore original lakefile
mv lakefile.lean.backup lakefile.lean
echo "Restored original lakefile.lean"

echo ""
echo "============================================"
echo "PHASE 5: Processing results"
echo "============================================"

# Process the log files to extract timing data
echo "module,normal_time,skipkernel_time" > timing_results.csv

while IFS= read -r module; do
  # Extract real time from normal build (format: real 0m1.234s)
  normal_log="benchmark_results/${module}.normal.log"
  skipkernel_log="benchmark_results/${module}.skipkernel.log"

  if [ -f "$normal_log" ] && [ -f "$skipkernel_log" ]; then
    normal_time=$(grep "^real" "$normal_log" | tail -1 | awk '{print $2}' || echo "0m0s")
    skipkernel_time=$(grep "^real" "$skipkernel_log" | tail -1 | awk '{print $2}' || echo "0m0s")

    echo "$module,$normal_time,$skipkernel_time" >> timing_results.csv
  else
    echo "Warning: Missing log files for $module"
  fi

done < mathlib_build_order.txt

echo ""
echo "============================================"
echo "Benchmarking complete!"
echo "============================================"
echo "Results saved to: timing_results.csv"
echo "Individual logs in: benchmark_results/"
echo ""
echo "Run the analysis script:"
echo "  python3 analyze_kernel_impact.py"
