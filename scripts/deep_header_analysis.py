#!/usr/bin/env python3
"""
Deep Recursive Header Analysis Pipeline for FeuerBird Exokernel
Synthesizes insights from multiple tools to understand the complete header architecture
"""

import os
import sys
import json
import subprocess
import re
import networkx as nx
import matplotlib.pyplot as plt
from pathlib import Path
from collections import defaultdict, Counter
from typing import Dict, List, Set, Tuple
import hashlib

class ExokernelHeaderAnalyzer:
    """Advanced header analysis for exokernel architecture"""
    
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.output_dir = self.project_root / "build" / "deep_analysis"
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Zone definitions for exokernel architecture
        self.zones = {
            'kernel': ['kernel/', 'include/'],
            'libos': ['libos/', 'include/libos/'],
            'rump': ['rump/', 'include/rump/'],
            'userland': ['user/', 'include/user/'],
            'applications': ['demos/', 'tests/']
        }
        
        # Header dependency graph
        self.dep_graph = nx.DiGraph()
        
        # Analysis results
        self.results = {
            'duplicates': defaultdict(list),
            'cycles': [],
            'complexity': {},
            'violations': [],
            'recommendations': [],
            'zone_violations': [],
            'header_stats': {}
        }
    
    def run_full_analysis(self):
        """Execute complete analysis pipeline"""
        print("=== FeuerBird Exokernel Deep Header Analysis Pipeline ===\n")
        
        # Phase 1: Discovery
        print("[1/10] Discovering all headers...")
        self.discover_headers()
        
        # Phase 2: Dependency extraction
        print("[2/10] Extracting dependencies...")
        self.extract_dependencies()
        
        # Phase 3: Zone boundary analysis
        print("[3/10] Analyzing zone boundaries...")
        self.analyze_zone_boundaries()
        
        # Phase 4: Cyclic dependency detection
        print("[4/10] Detecting dependency cycles...")
        self.detect_cycles()
        
        # Phase 5: Complexity analysis
        print("[5/10] Analyzing header complexity...")
        self.analyze_complexity()
        
        # Phase 6: Guard analysis
        print("[6/10] Checking header guards...")
        self.analyze_guards()
        
        # Phase 7: IWYU analysis
        print("[7/10] Running include-what-you-use...")
        self.run_iwyu()
        
        # Phase 8: Semantic analysis
        print("[8/10] Performing semantic analysis...")
        self.semantic_analysis()
        
        # Phase 9: Visualization
        print("[9/10] Generating visualizations...")
        self.generate_visualizations()
        
        # Phase 10: Synthesis
        print("[10/10] Synthesizing recommendations...")
        self.synthesize_recommendations()
        
        # Generate report
        self.generate_report()
        print(f"\n✓ Analysis complete! Results in: {self.output_dir}")
    
    def discover_headers(self):
        """Discover all headers and categorize by zone"""
        self.headers = defaultdict(list)
        self.all_headers = []
        
        for zone, paths in self.zones.items():
            for path_pattern in paths:
                path = self.project_root / path_pattern.rstrip('/')
                if path.exists():
                    for header in path.rglob("*.h"):
                        rel_path = header.relative_to(self.project_root)
                        self.headers[zone].append(str(rel_path))
                        self.all_headers.append(str(rel_path))
                        
                        # Check for duplicates
                        basename = header.name
                        self.results['duplicates'][basename].append({
                            'zone': zone,
                            'path': str(rel_path)
                        })
        
        # Identify problematic duplicates
        for basename, locations in self.results['duplicates'].items():
            if len(locations) > 1:
                zones = set(loc['zone'] for loc in locations)
                if len(zones) > 1:
                    self.results['violations'].append({
                        'type': 'cross_zone_duplicate',
                        'header': basename,
                        'zones': list(zones),
                        'paths': [loc['path'] for loc in locations]
                    })
    
    def extract_dependencies(self):
        """Extract include dependencies using multiple methods"""
        
        for header_path in self.all_headers:
            full_path = self.project_root / header_path
            
            # Add node to graph
            self.dep_graph.add_node(header_path, zone=self._get_zone(header_path))
            
            # Parse includes
            try:
                with open(full_path, 'r') as f:
                    content = f.read()
                    
                    # Find all includes
                    includes = re.findall(r'#include\s*[<"](.*?)[>"]', content)
                    
                    for included in includes:
                        # Resolve include path
                        resolved = self._resolve_include(included, header_path)
                        if resolved:
                            self.dep_graph.add_edge(header_path, resolved)
                            
                            # Check for zone violations
                            from_zone = self._get_zone(header_path)
                            to_zone = self._get_zone(resolved)
                            
                            if not self._is_valid_zone_dependency(from_zone, to_zone):
                                self.results['zone_violations'].append({
                                    'from': header_path,
                                    'to': resolved,
                                    'from_zone': from_zone,
                                    'to_zone': to_zone
                                })
            except Exception as e:
                print(f"  Warning: Could not parse {header_path}: {e}")
    
    def analyze_zone_boundaries(self):
        """Analyze dependencies across zone boundaries"""
        
        # Define allowed dependencies (from -> to)
        allowed_deps = {
            'kernel': [],  # Kernel should be self-contained
            'libos': ['kernel'],  # LibOS can depend on kernel
            'rump': ['kernel'],  # Rump can depend on kernel
            'userland': ['libos', 'kernel'],  # Userland can use libos/kernel
            'applications': ['userland', 'libos', 'kernel']  # Apps can use all
        }
        
        # Check all edges
        for from_node, to_node in self.dep_graph.edges():
            from_zone = self._get_zone(from_node)
            to_zone = self._get_zone(to_node)
            
            if from_zone and to_zone and from_zone != to_zone:
                if to_zone not in allowed_deps.get(from_zone, []):
                    self.results['violations'].append({
                        'type': 'illegal_zone_dependency',
                        'from': from_node,
                        'to': to_node,
                        'from_zone': from_zone,
                        'to_zone': to_zone,
                        'severity': 'high'
                    })
    
    def detect_cycles(self):
        """Detect circular dependencies at multiple levels"""
        
        # Direct cycles
        try:
            cycles = list(nx.simple_cycles(self.dep_graph))
            for cycle in cycles:
                self.results['cycles'].append({
                    'type': 'direct',
                    'headers': cycle,
                    'length': len(cycle)
                })
        except:
            pass
        
        # Zone-level cycles
        zone_graph = nx.DiGraph()
        for from_node, to_node in self.dep_graph.edges():
            from_zone = self._get_zone(from_node)
            to_zone = self._get_zone(to_node)
            if from_zone and to_zone and from_zone != to_zone:
                zone_graph.add_edge(from_zone, to_zone)
        
        try:
            zone_cycles = list(nx.simple_cycles(zone_graph))
            for cycle in zone_cycles:
                self.results['cycles'].append({
                    'type': 'zone',
                    'zones': cycle,
                    'severity': 'critical'
                })
        except:
            pass
    
    def analyze_complexity(self):
        """Analyze header complexity using multiple metrics"""
        
        for header_path in self.all_headers:
            full_path = self.project_root / header_path
            
            try:
                # Run complexity analysis
                result = subprocess.run(
                    ['lizard', str(full_path), '--csv'],
                    capture_output=True,
                    text=True
                )
                
                # Parse lizard output
                lines = result.stdout.strip().split('\n')
                if len(lines) > 1:
                    # Parse CSV header and data
                    metrics = {}
                    for line in lines[1:]:  # Skip header
                        parts = line.split(',')
                        if len(parts) >= 5:
                            metrics['cyclomatic_complexity'] = int(parts[1])
                            metrics['token_count'] = int(parts[2])
                            metrics['line_count'] = int(parts[3])
                    
                    self.results['complexity'][header_path] = metrics
                    
                    # Flag high complexity
                    if metrics.get('cyclomatic_complexity', 0) > 10:
                        self.results['violations'].append({
                            'type': 'high_complexity',
                            'header': header_path,
                            'complexity': metrics['cyclomatic_complexity']
                        })
                        
            except Exception as e:
                pass
    
    def analyze_guards(self):
        """Analyze header guard patterns"""
        
        guard_patterns = {
            'pragma_once': 0,
            'traditional': 0,
            'both': 0,
            'none': 0
        }
        
        for header_path in self.all_headers:
            full_path = self.project_root / header_path
            
            try:
                with open(full_path, 'r') as f:
                    content = f.read()
                    
                    has_pragma = '#pragma once' in content
                    has_ifndef = re.search(r'#ifndef\s+\w+_H', content) is not None
                    has_define = re.search(r'#define\s+\w+_H', content) is not None
                    
                    if has_pragma and (has_ifndef or has_define):
                        guard_patterns['both'] += 1
                    elif has_pragma:
                        guard_patterns['pragma_once'] += 1
                    elif has_ifndef and has_define:
                        guard_patterns['traditional'] += 1
                    else:
                        guard_patterns['none'] += 1
                        self.results['violations'].append({
                            'type': 'missing_guard',
                            'header': header_path
                        })
            except:
                pass
        
        self.results['header_stats']['guard_patterns'] = guard_patterns
    
    def run_iwyu(self):
        """Run include-what-you-use analysis"""
        
        # Sample some C files for IWYU analysis
        c_files = list(self.project_root.rglob("*.c"))[:10]
        
        for c_file in c_files:
            try:
                result = subprocess.run(
                    ['include-what-you-use', 
                     '-I', str(self.project_root / 'include'),
                     '-I', str(self.project_root / 'kernel'),
                     str(c_file)],
                    capture_output=True,
                    text=True,
                    timeout=5
                )
                
                # Parse IWYU output
                if 'should add' in result.stderr or 'should remove' in result.stderr:
                    self.results['recommendations'].append({
                        'file': str(c_file.relative_to(self.project_root)),
                        'iwyu_output': result.stderr
                    })
            except:
                pass
    
    def semantic_analysis(self):
        """Perform semantic analysis of header content"""
        
        # Analyze header content patterns
        patterns = {
            'types_only': [],
            'functions_only': [],
            'mixed': [],
            'guards_only': []
        }
        
        for header_path in self.all_headers:
            full_path = self.project_root / header_path
            
            try:
                with open(full_path, 'r') as f:
                    content = f.read()
                    
                    # Remove comments and preprocessor
                    clean_content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
                    clean_content = re.sub(r'//.*$', '', clean_content, flags=re.MULTILINE)
                    clean_content = re.sub(r'^#.*$', '', clean_content, flags=re.MULTILINE)
                    
                    has_typedef = 'typedef' in clean_content
                    has_struct = 'struct' in clean_content
                    has_function = bool(re.search(r'\w+\s*\([^)]*\)\s*;', clean_content))
                    has_extern = 'extern' in clean_content
                    
                    if not (has_typedef or has_struct or has_function or has_extern):
                        patterns['guards_only'].append(header_path)
                    elif (has_typedef or has_struct) and not (has_function or has_extern):
                        patterns['types_only'].append(header_path)
                    elif (has_function or has_extern) and not (has_typedef or has_struct):
                        patterns['functions_only'].append(header_path)
                    else:
                        patterns['mixed'].append(header_path)
            except:
                pass
        
        self.results['header_stats']['semantic_patterns'] = {
            k: len(v) for k, v in patterns.items()
        }
        
        # Recommend splitting mixed headers
        for header in patterns['mixed']:
            zone = self._get_zone(header)
            if zone in ['kernel', 'libos']:
                self.results['recommendations'].append({
                    'type': 'split_header',
                    'header': header,
                    'reason': 'Mixed types and functions in critical zone'
                })
    
    def generate_visualizations(self):
        """Generate various visualizations"""
        
        # 1. Zone dependency graph
        zone_graph = nx.DiGraph()
        zone_edges = defaultdict(int)
        
        for from_node, to_node in self.dep_graph.edges():
            from_zone = self._get_zone(from_node)
            to_zone = self._get_zone(to_node)
            if from_zone and to_zone:
                zone_edges[(from_zone, to_zone)] += 1
        
        for (from_zone, to_zone), count in zone_edges.items():
            zone_graph.add_edge(from_zone, to_zone, weight=count)
        
        # Save zone graph
        if zone_graph.nodes():
            plt.figure(figsize=(12, 8))
            pos = nx.spring_layout(zone_graph)
            nx.draw(zone_graph, pos, with_labels=True, node_color='lightblue',
                   node_size=3000, font_size=12, font_weight='bold',
                   arrows=True, arrowsize=20, edge_color='gray')
            
            # Add edge labels
            edge_labels = nx.get_edge_attributes(zone_graph, 'weight')
            nx.draw_networkx_edge_labels(zone_graph, pos, edge_labels)
            
            plt.title('FeuerBird Exokernel Zone Dependencies')
            plt.savefig(self.output_dir / 'zone_dependencies.png', dpi=150, bbox_inches='tight')
            plt.close()
        
        # 2. Header complexity heatmap
        if self.results['complexity']:
            headers = list(self.results['complexity'].keys())[:20]
            complexities = [self.results['complexity'][h].get('cyclomatic_complexity', 0) for h in headers]
            
            plt.figure(figsize=(10, 6))
            plt.barh(range(len(headers)), complexities)
            plt.yticks(range(len(headers)), [Path(h).name for h in headers])
            plt.xlabel('Cyclomatic Complexity')
            plt.title('Header Complexity Analysis')
            plt.tight_layout()
            plt.savefig(self.output_dir / 'header_complexity.png', dpi=150)
            plt.close()
        
        # 3. Dependency depth analysis
        depths = {}
        for node in self.dep_graph.nodes():
            try:
                # Calculate maximum depth from this node
                if self.dep_graph.out_degree(node) == 0:  # Leaf node
                    depth = 0
                else:
                    depth = max(nx.shortest_path_length(self.dep_graph, node, target).values()
                               for target in nx.descendants(self.dep_graph, node)) if nx.descendants(self.dep_graph, node) else 0
                depths[node] = depth
            except:
                depths[node] = 0
        
        # Save depth analysis
        with open(self.output_dir / 'dependency_depths.json', 'w') as f:
            json.dump(depths, f, indent=2)
    
    def synthesize_recommendations(self):
        """Synthesize actionable recommendations"""
        
        recommendations = []
        
        # 1. Duplicate resolution
        for basename, locations in self.results['duplicates'].items():
            if len(locations) > 1:
                zones = set(loc['zone'] for loc in locations)
                if len(zones) > 1:
                    recommendations.append({
                        'priority': 'HIGH',
                        'type': 'consolidate_duplicates',
                        'action': f'Consolidate {basename} - found in zones: {zones}',
                        'files': [loc['path'] for loc in locations],
                        'recommendation': f'Keep in include/ if public API, otherwise in specific zone'
                    })
        
        # 2. Cycle breaking
        for cycle in self.results['cycles']:
            if cycle['type'] == 'direct' and len(cycle['headers']) <= 3:
                recommendations.append({
                    'priority': 'CRITICAL',
                    'type': 'break_cycle',
                    'action': f'Break circular dependency',
                    'files': cycle['headers'],
                    'recommendation': 'Consider forward declarations or interface headers'
                })
        
        # 3. Zone boundary enforcement
        for violation in self.results['zone_violations']:
            recommendations.append({
                'priority': 'HIGH',
                'type': 'fix_zone_dependency',
                'action': f"Remove illegal dependency from {violation['from_zone']} to {violation['to_zone']}",
                'from': violation['from'],
                'to': violation['to'],
                'recommendation': 'Use interface headers or dependency injection'
            })
        
        # 4. Header organization
        recommendations.append({
            'priority': 'MEDIUM',
            'type': 'reorganize_structure',
            'action': 'Implement three-tier header organization',
            'recommendation': '''
            Tier 1 (include/): Public APIs and shared types
            Tier 2 (zone/include/): Zone-specific public interfaces  
            Tier 3 (zone/internal/): Zone-private implementations
            '''
        })
        
        self.results['final_recommendations'] = recommendations
    
    def generate_report(self):
        """Generate comprehensive analysis report"""
        
        report = []
        report.append("=" * 80)
        report.append("FEUERBIRD_EXOKERNEL DEEP HEADER ANALYSIS REPORT")
        report.append("=" * 80)
        report.append("")
        
        # Summary statistics
        report.append("SUMMARY STATISTICS")
        report.append("-" * 40)
        report.append(f"Total headers analyzed: {len(self.all_headers)}")
        report.append(f"Unique header names: {len(self.results['duplicates'])}")
        report.append(f"Cross-zone duplicates: {sum(1 for v in self.results['duplicates'].values() if len(v) > 1)}")
        report.append(f"Dependency cycles found: {len(self.results['cycles'])}")
        report.append(f"Zone violations: {len(self.results['zone_violations'])}")
        report.append(f"Total violations: {len(self.results['violations'])}")
        report.append("")
        
        # Zone distribution
        report.append("ZONE DISTRIBUTION")
        report.append("-" * 40)
        for zone, headers in self.headers.items():
            report.append(f"{zone:15} {len(headers):4} headers")
        report.append("")
        
        # Critical issues
        report.append("CRITICAL ISSUES")
        report.append("-" * 40)
        
        # Zone cycles
        zone_cycles = [c for c in self.results['cycles'] if c['type'] == 'zone']
        if zone_cycles:
            report.append("⚠️  Zone-level circular dependencies detected!")
            for cycle in zone_cycles:
                report.append(f"   {' -> '.join(cycle['zones'])} -> {cycle['zones'][0]}")
        
        # High-priority violations
        high_priority = [v for v in self.results['violations'] if v.get('severity') in ['high', 'critical']]
        if high_priority:
            report.append(f"⚠️  {len(high_priority)} high-priority violations found")
        report.append("")
        
        # Header guard analysis
        if 'guard_patterns' in self.results['header_stats']:
            report.append("HEADER GUARD PATTERNS")
            report.append("-" * 40)
            for pattern, count in self.results['header_stats']['guard_patterns'].items():
                report.append(f"{pattern:15} {count:4} headers")
        report.append("")
        
        # Semantic patterns
        if 'semantic_patterns' in self.results['header_stats']:
            report.append("HEADER CONTENT PATTERNS")
            report.append("-" * 40)
            for pattern, count in self.results['header_stats']['semantic_patterns'].items():
                report.append(f"{pattern:15} {count:4} headers")
        report.append("")
        
        # Top recommendations
        report.append("TOP RECOMMENDATIONS")
        report.append("-" * 40)
        
        critical_recs = [r for r in self.results.get('final_recommendations', []) 
                        if r['priority'] == 'CRITICAL'][:5]
        
        for i, rec in enumerate(critical_recs, 1):
            report.append(f"{i}. [{rec['priority']}] {rec['action']}")
            report.append(f"   {rec['recommendation']}")
            report.append("")
        
        # Save report
        report_text = '\n'.join(report)
        with open(self.output_dir / 'analysis_report.txt', 'w') as f:
            f.write(report_text)
        
        print(report_text)
        
        # Save detailed JSON results
        with open(self.output_dir / 'detailed_results.json', 'w') as f:
            json.dump(self.results, f, indent=2, default=str)
    
    def _get_zone(self, path: str) -> str:
        """Determine which zone a file belongs to"""
        for zone, patterns in self.zones.items():
            for pattern in patterns:
                if path.startswith(pattern.rstrip('/')):
                    return zone
        return 'unknown'
    
    def _resolve_include(self, include_path: str, from_file: str) -> str:
        """Resolve an include path to actual file"""
        # Try different include directories
        search_paths = [
            self.project_root / 'include',
            self.project_root / 'kernel',
            self.project_root / 'libos',
            self.project_root / Path(from_file).parent
        ]
        
        for search_path in search_paths:
            full_path = search_path / include_path
            if full_path.exists():
                return str(full_path.relative_to(self.project_root))
        
        return None
    
    def _is_valid_zone_dependency(self, from_zone: str, to_zone: str) -> bool:
        """Check if a zone dependency is valid"""
        if from_zone == to_zone:
            return True
        
        # Define allowed dependencies
        allowed = {
            'kernel': [],
            'libos': ['kernel'],
            'rump': ['kernel'],
            'userland': ['libos', 'kernel'],
            'applications': ['userland', 'libos', 'kernel', 'rump']
        }
        
        return to_zone in allowed.get(from_zone, [])


def main():
    if len(sys.argv) > 1:
        project_root = sys.argv[1]
    else:
        project_root = os.getcwd()
    
    analyzer = ExokernelHeaderAnalyzer(project_root)
    analyzer.run_full_analysis()


if __name__ == '__main__':
    main()