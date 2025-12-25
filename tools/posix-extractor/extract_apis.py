#!/usr/bin/env python3
"""
POSIX 2024 API Extractor
Extract machine-readable API specifications from SUSv5 HTML documentation.

Generates comprehensive JSON specification including:
- Function signatures and prototypes
- System call numbers and mappings  
- Data structures and constants
- Error codes and compatibility information
"""

import json
import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple
import argparse

try:
    from bs4 import BeautifulSoup, NavigableString, Tag
except ImportError:
    print("❌ Error: BeautifulSoup4 required. Install with: pip install beautifulsoup4")
    sys.exit(1)

@dataclass
class POSIXFunction:
    name: str
    return_type: str
    parameters: List[Dict[str, str]]
    description: str
    errors: List[str]
    includes: List[str]
    category: str
    source_file: str
    syscall_number: Optional[int] = None

@dataclass
class POSIXConstant:
    name: str
    value: Optional[str]
    description: str
    header: str

class POSIXExtractor:
    def __init__(self, susv5_dir: Path):
        self.susv5_dir = Path(susv5_dir)
        self.functions_dir = self.susv5_dir / "functions"
        self.basedefs_dir = self.susv5_dir / "basedefs"
        self.utilities_dir = self.susv5_dir / "utilities"
        
        # Standard syscall mappings (Linux x86_64 as reference)
        self.syscall_mappings = {
            'read': 0, 'write': 1, 'open': 2, 'close': 3, 'stat': 4,
            'fstat': 5, 'lstat': 6, 'poll': 7, 'lseek': 8, 'mmap': 9,
            'mprotect': 10, 'munmap': 11, 'brk': 12, 'rt_sigaction': 13,
            'rt_sigprocmask': 14, 'rt_sigreturn': 15, 'ioctl': 16,
            'pread64': 17, 'pwrite64': 18, 'readv': 19, 'writev': 20,
            'access': 21, 'pipe': 22, 'select': 23, 'sched_yield': 24,
            'mremap': 25, 'msync': 26, 'mincore': 27, 'madvise': 28,
            'shmget': 29, 'shmat': 30, 'shmctl': 31, 'dup': 32,
            'dup2': 33, 'pause': 34, 'nanosleep': 35, 'getitimer': 36,
            'alarm': 37, 'setitimer': 38, 'getpid': 39, 'sendfile': 40,
            'socket': 41, 'connect': 42, 'accept': 43, 'sendto': 44,
            'recvfrom': 45, 'sendmsg': 46, 'recvmsg': 47, 'shutdown': 48,
            'bind': 49, 'listen': 50, 'getsockname': 51, 'getpeername': 52,
            'socketpair': 53, 'setsockopt': 54, 'getsockopt': 55, 'clone': 56,
            'fork': 57, 'vfork': 58, 'execve': 59, 'exit': 60, 'wait4': 61
        }
        
        # Function categories
        self.categories = {
            'file': ['open', 'close', 'read', 'write', 'lseek', 'stat', 'fstat', 'lstat'],
            'process': ['fork', 'exec', 'exit', 'wait', 'getpid', 'kill'],
            'memory': ['mmap', 'munmap', 'mprotect', 'brk', 'sbrk'],
            'signal': ['signal', 'sigaction', 'sigprocmask', 'kill', 'raise'],
            'network': ['socket', 'bind', 'listen', 'accept', 'connect', 'send', 'recv'],
            'ipc': ['pipe', 'msgget', 'semget', 'shmget', 'mqueue'],
            'time': ['time', 'gettimeofday', 'clock_gettime', 'nanosleep'],
            'directory': ['opendir', 'readdir', 'closedir', 'mkdir', 'rmdir']
        }

    def extract_function_signature(self, soup: BeautifulSoup) -> Optional[Dict]:
        """Extract function signature from HTML."""
        # Look for function prototype
        synopsis = soup.find('h4', string='SYNOPSIS')
        if not synopsis:
            return None
            
        # Find code block after SYNOPSIS
        code_block = synopsis.find_next('pre') or synopsis.find_next('code')
        if not code_block:
            return None
            
        signature_text = code_block.get_text().strip()
        
        # Parse function signature using regex
        func_pattern = r'(\w+(?:\s*\*)*)\s+(\w+)\s*\((.*?)\)'
        match = re.search(func_pattern, signature_text, re.MULTILINE | re.DOTALL)
        
        if not match:
            return None
            
        return_type = match.group(1).strip()
        func_name = match.group(2).strip()
        params_str = match.group(3).strip()
        
        # Parse parameters
        parameters = []
        if params_str and params_str != 'void':
            # Split by comma, handling complex types
            param_parts = re.split(r',(?![^()]*\))', params_str)
            for param in param_parts:
                param = param.strip()
                if param:
                    # Extract parameter type and name
                    param_match = re.match(r'(.*?)(\w+)(?:\s*\[\s*\])?$', param)
                    if param_match:
                        param_type = param_match.group(1).strip()
                        param_name = param_match.group(2).strip()
                        parameters.append({
                            'type': param_type,
                            'name': param_name
                        })
        
        return {
            'name': func_name,
            'return_type': return_type,
            'parameters': parameters
        }

    def extract_includes(self, soup: BeautifulSoup) -> List[str]:
        """Extract required header files."""
        includes = []
        synopsis = soup.find('h4', string='SYNOPSIS')
        if synopsis:
            code_block = synopsis.find_next('pre') or synopsis.find_next('code')
            if code_block:
                text = code_block.get_text()
                # Find #include statements
                include_matches = re.findall(r'#include\s*<([^>]+)>', text)
                includes.extend(include_matches)
        return includes

    def extract_error_codes(self, soup: BeautifulSoup) -> List[str]:
        """Extract error codes from ERRORS section."""
        errors = []
        errors_section = soup.find('h4', string='ERRORS')
        if errors_section:
            # Find next section content
            content = errors_section.find_next_sibling()
            while content and content.name != 'h4':
                if content.name == 'dl':
                    # Definition list of errors
                    for dt in content.find_all('dt'):
                        error_code = dt.get_text().strip()
                        if error_code.startswith('E'):
                            errors.append(error_code)
                elif content.string and 'E' in content.string:
                    # Extract error codes from text
                    error_matches = re.findall(r'\b(E[A-Z]+)\b', content.string)
                    errors.extend(error_matches)
                content = content.find_next_sibling()
        return list(set(errors))  # Remove duplicates

    def extract_description(self, soup: BeautifulSoup) -> str:
        """Extract function description."""
        desc_section = soup.find('h4', string='DESCRIPTION')
        if desc_section:
            # Get first paragraph after description
            para = desc_section.find_next('p')
            if para:
                return para.get_text().strip()[:200] + '...'  # Truncate for brevity
        return ""

    def categorize_function(self, func_name: str) -> str:
        """Determine function category."""
        for category, functions in self.categories.items():
            if func_name in functions:
                return category
        return "misc"

    def extract_functions(self) -> List[POSIXFunction]:
        """Extract all POSIX functions from HTML documentation."""
        functions = []
        
        if not self.functions_dir.exists():
            print(f"❌ Functions directory not found: {self.functions_dir}")
            return functions
            
        print(f"📖 Extracting functions from {self.functions_dir}")
        
        for html_file in sorted(self.functions_dir.glob("*.html")):
            try:
                with open(html_file, 'r', encoding='utf-8') as f:
                    soup = BeautifulSoup(f.read(), 'html.parser')
                
                signature = self.extract_function_signature(soup)
                if signature:
                    func_name = signature['name']
                    
                    posix_func = POSIXFunction(
                        name=func_name,
                        return_type=signature['return_type'],
                        parameters=signature['parameters'],
                        description=self.extract_description(soup),
                        errors=self.extract_error_codes(soup),
                        includes=self.extract_includes(soup),
                        category=self.categorize_function(func_name),
                        source_file=str(html_file.relative_to(self.susv5_dir)),
                        syscall_number=self.syscall_mappings.get(func_name)
                    )
                    
                    functions.append(posix_func)
                    
            except Exception as e:
                print(f"⚠️  Error processing {html_file}: {e}")
                continue
        
        print(f"✅ Extracted {len(functions)} POSIX functions")
        return functions

    def extract_constants(self) -> List[POSIXConstant]:
        """Extract POSIX constants and macros."""
        constants = []
        
        # Key header files to parse
        key_headers = [
            'errno.h.html', 'fcntl.h.html', 'sys_stat.h.html', 
            'signal.h.html', 'unistd.h.html', 'sys_types.h.html'
        ]
        
        for header in key_headers:
            header_file = self.basedefs_dir / header
            if header_file.exists():
                try:
                    with open(header_file, 'r', encoding='utf-8') as f:
                        soup = BeautifulSoup(f.read(), 'html.parser')
                    
                    # Find constant definitions
                    for code_block in soup.find_all(['pre', 'code']):
                        text = code_block.get_text()
                        # Look for #define statements
                        defines = re.findall(r'#define\s+(\w+)\s+([^\n]*)', text)
                        for name, value in defines:
                            if name.isupper() or name.startswith('_'):
                                constants.append(POSIXConstant(
                                    name=name,
                                    value=value.strip(),
                                    description=f"From {header}",
                                    header=header.replace('.html', '')
                                ))
                                
                except Exception as e:
                    print(f"⚠️  Error processing {header}: {e}")
        
        print(f"✅ Extracted {len(constants)} POSIX constants")
        return constants

    def generate_json_spec(self) -> Dict:
        """Generate complete JSON specification."""
        print("🔬 Generating POSIX 2024 machine-readable specification...")
        
        functions = self.extract_functions()
        constants = self.extract_constants()
        
        # Organize functions by category
        functions_by_category = {}
        for func in functions:
            category = func.category
            if category not in functions_by_category:
                functions_by_category[category] = []
            functions_by_category[category].append({
                'name': func.name,
                'return_type': func.return_type,
                'parameters': func.parameters,
                'description': func.description,
                'errors': func.errors,
                'includes': func.includes,
                'syscall_number': func.syscall_number,
                'source_file': func.source_file
            })
        
        # Create comprehensive specification
        spec = {
            'metadata': {
                'version': 'POSIX.1-2024',
                'standard': 'IEEE Std 1003.1-2024',
                'generated_by': 'FeuerBird POSIX Extractor v1.0',
                'c_standard': 'ISO/IEC 9899:2018 (C17)',
                'generation_date': '2025-01-09'
            },
            'statistics': {
                'total_functions': len(functions),
                'total_constants': len(constants),
                'categories': list(self.categories.keys()),
                'syscalls_mapped': len([f for f in functions if f.syscall_number is not None])
            },
            'functions': functions_by_category,
            'constants': {
                const.header: [
                    {'name': c.name, 'value': c.value, 'description': c.description}
                    for c in constants if c.header == const.header
                ] for const in set(c.header for c in constants)
            },
            'syscall_mappings': self.syscall_mappings,
            'compatibility': {
                'feuerbird': {
                    'missing_syscalls': [name for name, num in self.syscall_mappings.items() 
                                       if name not in ['fork', 'exit', 'wait', 'pipe', 'kill', 
                                                     'exec', 'getpid', 'sleep']],
                    'native_equivalents': {
                        'read': 'exo_read_optimized',
                        'write': 'exo_write_optimized',
                        'mmap': 'exo_alloc_page',
                        'fork': 'SYS_fork',
                        'exec': 'SYS_exec'
                    }
                }
            }
        }
        
        return spec

def main():
    parser = argparse.ArgumentParser(description='Extract POSIX 2024 APIs to machine-readable format')
    parser.add_argument('susv5_dir', nargs='?', 
                       default='doc/standards/susv5-html',
                       help='Path to SUSv5 HTML directory (default: doc/standards/susv5-html)')
    parser.add_argument('--output', '-o', 
                       default='config/posix2024_apis.json',
                       help='Output JSON file (default: config/posix2024_apis.json)')
    parser.add_argument('--pretty', action='store_true',
                       help='Pretty-print JSON output')
    
    args = parser.parse_args()
    
    susv5_dir = Path(args.susv5_dir)
    if not susv5_dir.exists():
        print(f"❌ SUSv5 directory not found: {susv5_dir}")
        print("Expected structure: susv5-html/functions/, susv5-html/basedefs/")
        return 1
    
    print(f"🚀 FeuerBird POSIX 2024 API Extractor")
    print(f"=====================================")
    print(f"📂 Source: {susv5_dir}")
    print(f"📄 Output: {args.output}")
    print()
    
    extractor = POSIXExtractor(susv5_dir)
    spec = extractor.generate_json_spec()
    
    # Write JSON specification
    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_path, 'w') as f:
        if args.pretty:
            json.dump(spec, f, indent=2, sort_keys=True)
        else:
            json.dump(spec, f)
    
    print(f"✅ Generated machine-readable POSIX 2024 specification: {output_path}")
    print(f"📊 Functions: {spec['statistics']['total_functions']}")
    print(f"📊 Constants: {spec['statistics']['total_constants']}")
    print(f"📊 Syscalls mapped: {spec['statistics']['syscalls_mapped']}")
    print()
    print("🎯 Specification ready for FeuerBird POSIX compatibility implementation!")
    
    return 0

if __name__ == '__main__':
    sys.exit(main())