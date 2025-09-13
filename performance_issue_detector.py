#!/usr/bin/env python3
"""
🔍 CERTEUS Performance Issues Analysis
Identyfikacja bottlenecks i problemów wydajnościowych
"""

import ast
import os
from typing import Any


class PerformanceIssueDetector:
    """Detektor problemów wydajnościowych w kodzie"""

    def __init__(self):
        self.issues = []
        self.performance_patterns = {
            'blocking_calls': ['time.sleep', 'input(', 'print('],
            'inefficient_loops': ['for.*in.*range', 'while True:'],
            'memory_issues': ['list()', 'dict()', '*=', '+='],
            'io_issues': ['open(', 'read(', 'write('],
            'sync_in_async': ['requests.', 'urllib.', 'time.sleep']
        }

    def analyze_file(self, filepath: str) -> dict[str, Any]:
        """Analiza pliku pod kątem problemów wydajnościowych"""

        if not os.path.exists(filepath):
            return {'error': f'File {filepath} not found'}

        try:
            with open(filepath, encoding='utf-8') as f:
                content = f.read()

            # Analiza AST
            tree = ast.parse(content, filename=filepath)

            issues = {
                'blocking_operations': [],
                'potential_memory_leaks': [],
                'inefficient_patterns': [],
                'missing_optimizations': []
            }

            # Szukaj problematycznych wzorców
            for node in ast.walk(tree):
                if isinstance(node, ast.Call):
                    self._analyze_function_call(node, issues)
                elif isinstance(node, ast.For):
                    self._analyze_loop(node, issues)
                elif isinstance(node, ast.While):
                    self._analyze_while_loop(node, issues)

            return {
                'file': filepath,
                'issues': issues,
                'line_count': len(content.split('\n')),
                'complexity_score': self._calculate_complexity(tree)
            }

        except Exception as e:
            return {'error': f'Error analyzing {filepath}: {e}'}

    def _analyze_function_call(self, node: ast.Call, issues: dict):
        """Analiza wywołań funkcji"""

        func_name = self._get_function_name(node)

        # Blocking operations
        if any(pattern in func_name for pattern in ['sleep', 'wait', 'join']):
            issues['blocking_operations'].append({
                'type': 'blocking_call',
                'function': func_name,
                'line': node.lineno
            })

        # Potential memory issues
        if func_name in ['list', 'dict', 'set'] and not node.args:
            issues['potential_memory_leaks'].append({
                'type': 'empty_container_creation',
                'function': func_name,
                'line': node.lineno
            })

    def _analyze_loop(self, node: ast.For, issues: dict):
        """Analiza pętli for"""

        # Check for range(len(x)) pattern
        if (isinstance(node.iter, ast.Call) and
            isinstance(node.iter.func, ast.Name) and
            node.iter.func.id == 'range'):

            if (node.iter.args and
                isinstance(node.iter.args[0], ast.Call) and
                isinstance(node.iter.args[0].func, ast.Name) and
                node.iter.args[0].func.id == 'len'):

                issues['inefficient_patterns'].append({
                    'type': 'range_len_pattern',
                    'line': node.lineno,
                    'suggestion': 'Use enumerate() or direct iteration'
                })

    def _analyze_while_loop(self, node: ast.While, issues: dict):
        """Analiza pętli while"""

        # Check for while True without break
        if (isinstance(node.test, ast.Constant) and
            node.test.value is True):

            has_break = any(isinstance(n, ast.Break) for n in ast.walk(node))
            if not has_break:
                issues['inefficient_patterns'].append({
                    'type': 'infinite_loop_without_break',
                    'line': node.lineno,
                    'severity': 'high'
                })

    def _get_function_name(self, node: ast.Call) -> str:
        """Pobierz nazwę funkcji z node AST"""

        if isinstance(node.func, ast.Name):
            return node.func.id
        elif isinstance(node.func, ast.Attribute):
            return f"{node.func.attr}"
        else:
            return "unknown"

    def _calculate_complexity(self, tree: ast.AST) -> int:
        """Oblicz complexity score"""

        complexity = 0
        for node in ast.walk(tree):
            if isinstance(node, ast.If | ast.For | ast.While | ast.With):
                complexity += 1
            elif isinstance(node, ast.Try):
                complexity += 2

        return complexity

    def analyze_ultra_scale_systems(self) -> dict:
        """Analiza wszystkich ultra-scale systemów"""

        ultra_scale_files = [
            'ultra_performance_ledger.py',
            'zero_latency_pipeline.py',
            'hardware_optimizations.py',
            'distributed_ultra_scale.py',
            'world_class_monitoring.py',
            'impossible_scale_test.py'
        ]

        results = {}
        for file in ultra_scale_files:
            results[file] = self.analyze_file(file)

        return results


def main():
    """Main analysis function"""

    print("🔍 PERFORMANCE ISSUES ANALYSIS")
    print("=" * 50)

    detector = PerformanceIssueDetector()
    results = detector.analyze_ultra_scale_systems()

    total_issues = 0
    critical_issues = 0

    for filename, analysis in results.items():
        if 'error' in analysis:
            print(f"❌ {filename}: {analysis['error']}")
            continue

        print(f"\n📁 {filename}:")
        print(f"   Lines: {analysis.get('line_count', 0)}")
        print(f"   Complexity: {analysis.get('complexity_score', 0)}")

        issues = analysis.get('issues', {})
        file_issue_count = 0

        for category, issue_list in issues.items():
            if issue_list:
                print(f"   ⚠️ {category}: {len(issue_list)} issues")
                for issue in issue_list[:3]:  # Show first 3 issues
                    severity = issue.get('severity', 'medium')
                    line = issue.get('line', 'unknown')
                    issue_type = issue.get('type', 'unknown')
                    print(f"      - Line {line}: {issue_type} ({severity})")

                    if severity == 'high':
                        critical_issues += 1
                    file_issue_count += 1

                if len(issue_list) > 3:
                    print(f"      ... and {len(issue_list) - 3} more")

        total_issues += file_issue_count

        if file_issue_count == 0:
            print("   ✅ No performance issues detected")

    print("\n📊 SUMMARY:")
    print(f"   Total Issues: {total_issues}")
    print(f"   Critical Issues: {critical_issues}")

    if critical_issues > 0:
        print("🚨 CRITICAL ISSUES DETECTED - IMMEDIATE ACTION REQUIRED")
    elif total_issues > 0:
        print("⚠️ Performance issues found - review recommended")
    else:
        print("✅ No significant performance issues detected")


if __name__ == "__main__":
    main()
