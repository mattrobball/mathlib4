#!/usr/bin/env python3
"""
Analyze the impact of kernel typechecking on Mathlib build times.
"""

import csv
import sys
from pathlib import Path


def parse_time(time_str):
    """Convert time string (e.g., '1m30.5s' or '45.2s') to seconds."""
    if not time_str or time_str.strip() == '':
        return None

    time_str = time_str.strip()

    # Handle format like "1m30.5s"
    if 'm' in time_str:
        parts = time_str.split('m')
        minutes = float(parts[0])
        seconds = float(parts[1].rstrip('s'))
        return minutes * 60 + seconds
    # Handle format like "45.2s"
    elif 's' in time_str:
        return float(time_str.rstrip('s'))
    # Already a number
    else:
        return float(time_str)


def analyze_results(csv_file):
    """Analyze timing results and identify files with highest kernel TC impact."""

    results = []

    with open(csv_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            module = row['module']
            normal_time = parse_time(row['normal_time'])
            skipkernel_time = parse_time(row['skipkernel_time'])

            if normal_time is None or skipkernel_time is None:
                continue

            if skipkernel_time == 0:
                # Avoid division by zero
                pct_diff = float('inf') if normal_time > 0 else 0
            else:
                # Percentage: (normal - skip) / skip * 100
                # Positive means normal is slower (kernel TC takes time)
                pct_diff = ((normal_time - skipkernel_time) / skipkernel_time) * 100

            time_diff = normal_time - skipkernel_time

            results.append({
                'module': module,
                'normal_time': normal_time,
                'skipkernel_time': skipkernel_time,
                'time_diff': time_diff,
                'pct_diff': pct_diff
            })

    # Sort by percentage difference (descending)
    results.sort(key=lambda x: x['pct_diff'], reverse=True)

    return results


def print_report(results, top_n=50):
    """Print a report of the top N files by kernel TC impact."""

    print("=" * 100)
    print(f"TOP {top_n} FILES WITH HIGHEST KERNEL TYPECHECKING IMPACT")
    print("=" * 100)
    print()
    print(f"{'Rank':<6} {'Module':<60} {'Normal':<12} {'Skip TC':<12} {'Diff':<12} {'% Diff':<10}")
    print("-" * 100)

    for i, result in enumerate(results[:top_n], 1):
        print(f"{i:<6} {result['module']:<60} "
              f"{result['normal_time']:>10.2f}s {result['skipkernel_time']:>10.2f}s "
              f"{result['time_diff']:>10.2f}s {result['pct_diff']:>9.1f}%")

    print()
    print("=" * 100)
    print("SUMMARY STATISTICS")
    print("=" * 100)

    if results:
        total_normal = sum(r['normal_time'] for r in results)
        total_skip = sum(r['skipkernel_time'] for r in results)
        total_diff = total_normal - total_skip
        avg_pct = (total_diff / total_skip * 100) if total_skip > 0 else 0

        print(f"Total modules analyzed: {len(results)}")
        print(f"Total time (normal):    {total_normal:.2f}s ({total_normal/3600:.2f}h)")
        print(f"Total time (skip TC):   {total_skip:.2f}s ({total_skip/3600:.2f}h)")
        print(f"Total time saved:       {total_diff:.2f}s ({total_diff/3600:.2f}h)")
        print(f"Average % difference:   {avg_pct:.1f}%")
        print()

        # Count files with >X% impact
        high_impact_50 = len([r for r in results if r['pct_diff'] > 50])
        high_impact_100 = len([r for r in results if r['pct_diff'] > 100])
        high_impact_200 = len([r for r in results if r['pct_diff'] > 200])

        print(f"Files with >50% impact:  {high_impact_50}")
        print(f"Files with >100% impact: {high_impact_100}")
        print(f"Files with >200% impact: {high_impact_200}")


def save_detailed_report(results, output_file='kernel_impact_detailed.csv'):
    """Save detailed results to a CSV file."""

    with open(output_file, 'w', newline='') as f:
        fieldnames = ['rank', 'module', 'normal_time', 'skipkernel_time',
                     'time_diff', 'pct_diff']
        writer = csv.DictWriter(f, fieldnames=fieldnames)

        writer.writeheader()
        for i, result in enumerate(results, 1):
            writer.writerow({
                'rank': i,
                'module': result['module'],
                'normal_time': f"{result['normal_time']:.2f}",
                'skipkernel_time': f"{result['skipkernel_time']:.2f}",
                'time_diff': f"{result['time_diff']:.2f}",
                'pct_diff': f"{result['pct_diff']:.1f}"
            })

    print(f"\nDetailed results saved to: {output_file}")


if __name__ == '__main__':
    csv_file = 'timing_results.csv'

    if len(sys.argv) > 1:
        csv_file = sys.argv[1]

    if not Path(csv_file).exists():
        print(f"Error: {csv_file} not found")
        sys.exit(1)

    print(f"Analyzing results from: {csv_file}")
    print()

    results = analyze_results(csv_file)
    print_report(results, top_n=100)
    save_detailed_report(results)
