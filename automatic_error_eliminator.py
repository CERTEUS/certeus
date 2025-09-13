#!/usr/bin/env python3
"""
CERTEUS Automatic Error Elimination System
Automated fixing of identified issues across the project.
"""

import ast
import os
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Set, Tuple


@dataclass
class Fix:
    """Represents a code fix to be applied"""
    file_path: str
    line_number: int
    original_code: str
    fixed_code: str
    description: str
    category: str

class CERTEUSErrorEliminator:
    """Automated error fixing system for CERTEUS project"""

    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.fixes_applied = []
        self.backup_dir = self.project_root / "backups"

    def create_backup(self, file_path: str):
        """Create backup of file before modification"""
        self.backup_dir.mkdir(exist_ok=True)
        src = Path(file_path)
        dst = self.backup_dir / f"{src.name}.backup"
        shutil.copy2(src, dst)

    def fix_performance_issues(self) -> List[Fix]:
        """Fix blocking operations and performance issues"""
        fixes = []

        ultra_scale_files = [
            "ultra_performance_ledger.py",
            "zero_latency_pipeline.py",
            "hardware_optimizations.py",
            "distributed_ultra_scale.py",
            "world_class_monitoring.py",
            "impossible_scale_test.py"
        ]

        for filename in ultra_scale_files:
            file_path = self.project_root / filename
            if file_path.exists():
                fixes.extend(self._fix_file_performance(str(file_path)))

        return fixes

    def _fix_file_performance(self, file_path: str) -> List[Fix]:
        """Fix performance issues in a single file"""
        fixes = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.splitlines()

            # Fix 1: Replace blocking time.sleep() with asyncio.sleep()
            if 'time.sleep' in content and 'asyncio' not in content:
                new_content = content.replace('import time', 'import asyncio')
                new_content = new_content.replace('time.sleep(', 'await asyncio.sleep(')

                if new_content != content:
                    self.create_backup(file_path)
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(new_content)

                    fixes.append(Fix(
                        file_path=file_path,
                        line_number=0,
                        original_code="time.sleep()",
                        fixed_code="await asyncio.sleep()",
                        description="Replaced blocking sleep with async sleep",
                        category="PERFORMANCE"
                    ))

            # Fix 2: Add proper async context managers
            if 'class' in content and '__enter__' not in content:
                # Look for classes that need async context managers
                for i, line in enumerate(lines):
                    if 'class' in line and 'Ledger' in line:
                        # Add async context manager methods
                        indent = '    '
                        context_manager_code = f"""
{indent}async def __aenter__(self):
{indent}    await self.connect()
{indent}    return self

{indent}async def __aexit__(self, exc_type, exc_val, exc_tb):
{indent}    await self.close()
{indent}    return False
"""
                        # Insert after class definition
                        lines.insert(i + 1, context_manager_code)

                        fixes.append(Fix(
                            file_path=file_path,
                            line_number=i + 1,
                            original_code=line,
                            fixed_code=line + context_manager_code,
                            description="Added async context manager",
                            category="PERFORMANCE"
                        ))
                        break

            # Fix 3: Replace hardcoded passwords with environment variables
            for i, line in enumerate(lines):
                if 'password=' in line and '"' in line:
                    # Extract password assignment
                    if '"supersecret"' in line or '"password"' in line:
                        fixed_line = line.replace(
                            'password=os.getenv("DATABASE_PASSWORD", "")',
                            'password=os.getenv("DATABASE_PASSWORD", "")'
                        ).replace(
                            'password=os.getenv("DATABASE_PASSWORD", "")',
                            'password=os.getenv("DATABASE_PASSWORD", "")'
                        )

                        if fixed_line != line:
                            lines[i] = fixed_line
                            fixes.append(Fix(
                                file_path=file_path,
                                line_number=i + 1,
                                original_code=line.strip(),
                                fixed_code=fixed_line.strip(),
                                description="Replaced hardcoded password with environment variable",
                                category="SECURITY"
                            ))

            # Apply line-based fixes
            if any(fix.category in ["SECURITY"] for fix in fixes):
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write('\n'.join(lines))

        except Exception as e:
            print(f"Error fixing {file_path}: {e}")

        return fixes

    def fix_security_vulnerabilities(self) -> List[Fix]:
        """Fix security vulnerabilities across the project"""
        fixes = []

        # Fix MD5 usage to SHA-256
        for py_file in self.project_root.rglob("*.py"):
            fixes.extend(self._fix_weak_crypto(str(py_file)))
            fixes.extend(self._fix_hardcoded_secrets(str(py_file)))

        return fixes

    def _fix_weak_crypto(self, file_path: str) -> List[Fix]:
        """Replace weak cryptographic algorithms"""
        fixes = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()

            original_content = content

            # Replace MD5 with SHA-256
            if 'hashlib.sha256' in content:
                content = content.replace('hashlib.sha256', 'hashlib.sha256')
                content = content.replace('[:16]', '[:16]')  # Adjust hash length

            # Replace SHA1 with SHA-256
            if 'hashlib.sha256' in content:
                content = content.replace('hashlib.sha256', 'hashlib.sha256')

            if content != original_content:
                self.create_backup(file_path)
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(content)

                fixes.append(Fix(
                    file_path=file_path,
                    line_number=0,
                    original_code="hashlib.sha256/sha1",
                    fixed_code="hashlib.sha256",
                    description="Upgraded weak crypto to SHA-256",
                    category="SECURITY"
                ))

        except Exception as e:
            print(f"Error fixing crypto in {file_path}: {e}")

        return fixes

    def _fix_hardcoded_secrets(self, file_path: str) -> List[Fix]:
        """Fix hardcoded secrets and credentials"""
        fixes = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            modified = False

            for i, line in enumerate(lines):
                original_line = line

                # Fix hardcoded passwords
                if 'password=' in line and '"' in line:
                    # Skip test files
                    if '/tests/' in file_path or 'test_' in file_path:
                        continue

                    if '"supersecret"' in line:
                        line = line.replace(
                            '"supersecret"',
                            'os.getenv("DATABASE_PASSWORD", "")'
                        )
                        modified = True

                    if '"password"' in line and '=' in line:
                        line = line.replace(
                            '"password"',
                            'os.getenv("DATABASE_PASSWORD", "")'
                        )
                        modified = True

                # Fix API keys
                if 'api_key=' in line and '"' in line:
                    if '/tests/' not in file_path:
                        line = re.sub(
                            r'api_key\s*=\s*"[^"]*"',
                            'api_key=os.getenv("API_KEY", "")',
                            line
                        )
                        modified = True

                if line != original_line:
                    lines[i] = line
                    fixes.append(Fix(
                        file_path=file_path,
                        line_number=i + 1,
                        original_code=original_line.strip(),
                        fixed_code=line.strip(),
                        description="Replaced hardcoded secret with environment variable",
                        category="SECURITY"
                    ))

            # Add os import if needed
            if modified and 'import os' not in ''.join(lines[:10]):
                lines.insert(0, 'import os\n')
                fixes.append(Fix(
                    file_path=file_path,
                    line_number=1,
                    original_code="",
                    fixed_code="import os",
                    description="Added os import for environment variables",
                    category="SECURITY"
                ))

            if modified:
                self.create_backup(file_path)
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.writelines(lines)

        except Exception as e:
            print(f"Error fixing secrets in {file_path}: {e}")

        return fixes

    def fix_dangerous_functions(self) -> List[Fix]:
        """Fix usage of dangerous functions"""
        fixes = []

        for py_file in self.project_root.rglob("*.py"):
            if '/tests/' in str(py_file):
                continue  # Skip test files

            fixes.extend(self._fix_file_dangerous_functions(str(py_file)))

        return fixes

    def _fix_file_dangerous_functions(self, file_path: str) -> List[Fix]:
        """Fix dangerous functions in a single file"""
        fixes = []

        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.splitlines()

            for i, line in enumerate(lines):
                original_line = line

                # Replace eval() with safer alternatives  # WARNING: eval() is dangerous - consider ast.literal_eval()
                if 'eval(' in line:  # WARNING: eval() is dangerous - consider ast.literal_eval()
                    # Add comment about unsafe usage
                    lines[i] = line + '  # WARNING: eval() is dangerous - consider ast.literal_eval()'  # WARNING: eval() is dangerous - consider ast.literal_eval()
                    fixes.append(Fix(
                        file_path=file_path,
                        line_number=i + 1,
                        original_code=original_line,
                        fixed_code=lines[i],
                        description="Added warning about dangerous eval() usage",  # WARNING: eval() is dangerous - consider ast.literal_eval()
                        category="SECURITY"
                    ))

                # Replace exec() with warnings  # WARNING: exec() is dangerous - avoid dynamic code execution
                if 'exec(' in line:  # WARNING: exec() is dangerous - avoid dynamic code execution
                    lines[i] = line + '  # WARNING: exec() is dangerous - avoid dynamic code execution'  # WARNING: exec() is dangerous - avoid dynamic code execution
                    fixes.append(Fix(
                        file_path=file_path,
                        line_number=i + 1,
                        original_code=original_line,
                        fixed_code=lines[i],
                        description="Added warning about dangerous exec() usage",  # WARNING: exec() is dangerous - avoid dynamic code execution
                        category="SECURITY"
                    ))

            if fixes:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write('\n'.join(lines))

        except Exception as e:
            print(f"Error fixing dangerous functions in {file_path}: {e}")

        return fixes

    def generate_fix_report(self, all_fixes: List[Fix]):
        """Generate comprehensive fix report"""
        print("=" * 80)
        print("🔧 CERTEUS AUTOMATIC ERROR ELIMINATION REPORT")
        print("=" * 80)

        if not all_fixes:
            print("✅ No fixes were needed!")
            return

        category_counts = {}
        for fix in all_fixes:
            category_counts[fix.category] = category_counts.get(fix.category, 0) + 1

        print(f"\n📊 FIXES APPLIED:")
        print(f"   Total Fixes: {len(all_fixes)}")
        print(f"   🔒 SECURITY: {category_counts.get('SECURITY', 0)}")
        print(f"   ⚡ PERFORMANCE: {category_counts.get('PERFORMANCE', 0)}")
        print(f"   🛡️  SAFETY: {category_counts.get('SAFETY', 0)}")

        print(f"\n📄 DETAILED FIXES:")
        print("-" * 80)

        # Group fixes by file
        file_fixes = {}
        for fix in all_fixes:
            file_name = os.path.basename(fix.file_path)
            if file_name not in file_fixes:
                file_fixes[file_name] = []
            file_fixes[file_name].append(fix)

        for file_name, fixes in sorted(file_fixes.items()):
            print(f"\n📁 {file_name}")
            print(f"   Fixes: {len(fixes)}")

            for fix in fixes:
                emoji = {'SECURITY': '🔒', 'PERFORMANCE': '⚡', 'SAFETY': '🛡️'}.get(fix.category, '🔧')
                print(f"   {emoji} Line {fix.line_number}: {fix.description}")
                if fix.original_code and fix.fixed_code:
                    print(f"      Before: {fix.original_code[:60]}...")
                    print(f"      After:  {fix.fixed_code[:60]}...")
                print()

    def run_complete_elimination(self):
        """Run complete error elimination process"""
        print("🔧 Starting CERTEUS Automatic Error Elimination...")

        all_fixes = []

        print("⚡ Fixing performance issues...")
        all_fixes.extend(self.fix_performance_issues())

        print("🔒 Fixing security vulnerabilities...")
        all_fixes.extend(self.fix_security_vulnerabilities())

        print("🛡️ Fixing dangerous functions...")
        all_fixes.extend(self.fix_dangerous_functions())

        self.generate_fix_report(all_fixes)

        print(f"\n💾 Backups created in: {self.backup_dir}")
        print("✅ Error elimination completed!")

        return all_fixes

if __name__ == "__main__":
    # Run error elimination on CERTEUS project
    certeus_root = "f:/projekty/control/workspaces/certeus"

    eliminator = CERTEUSErrorEliminator(certeus_root)
    fixes = eliminator.run_complete_elimination()

    print(f"\n🎯 Total issues fixed: {len(fixes)}")
