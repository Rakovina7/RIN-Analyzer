#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RIN Analyzer GUI - Residue Interaction Network Analysis Tool
WITH POCKET DETECTION, MULTI-FACTOR CONSENSUS SCORING & PUBLICATION-READY VISUALIZATION
Version: 7.0.0 - Ligand-Free Edition with Enhanced PyMOL Visualization

This version includes:
- Cross-platform support (Windows, macOS, Linux)
- Full Plotly visualizations
- Pocket Detection & Consensus Scoring engine
- Complete Validation Engine with PyMOL exports
- REMOVED: All ligand-related functionality
- UPGRADED: Publication-quality PyMOL visualization
"""

import sys
import os
import shutil
import json
import traceback
import subprocess
import tempfile
import math
import stat
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Set, Union, NamedTuple
from dataclasses import dataclass, field
from enum import Enum
from abc import ABC, abstractmethod
import warnings
warnings.filterwarnings("ignore")

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QPushButton, QLabel, QListWidget, QListWidgetItem, QFileDialog,
    QTabWidget, QTextEdit, QProgressBar, QSplitter, QMessageBox,
    QGroupBox, QScrollArea, QTableWidget, QTableWidgetItem,
    QHeaderView, QToolBar, QStatusBar, QComboBox, QLineEdit,
    QFormLayout, QGridLayout, QDoubleSpinBox, QSpinBox, QCheckBox,
    QFrame, QSlider
)
from PyQt6.QtCore import (
    Qt, QThread, pyqtSignal as Signal, pyqtSlot as Slot, 
    QTimer, QUrl, QSize
)
from PyQt6.QtGui import (
    QPixmap, QIcon, QFont, QAction, QPalette, QColor
)
from PyQt6.QtWebEngineWidgets import QWebEngineView

import pandas as pd
import numpy as np
import networkx as nx
import scipy.sparse.linalg
import scipy.linalg
from scipy.spatial import cKDTree
from Bio.PDB import PDBParser, MMCIFParser, PDBIO, Select
from Bio.PDB.Model import Model
from Bio.PDB.Structure import Structure
from Bio.PDB.Residue import Residue
import matplotlib
matplotlib.use('Agg')
import plotly.graph_objects as go
from tqdm import tqdm
import re
import glob
import gzip
from functools import lru_cache
from collections import defaultdict
import logging
import urllib.request
import urllib.error

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')

DEFAULT_CUTOFF = 4.5
DEFAULT_TOP_PERCENTILE = 0.95
APP_NAME = "RIN Analyzer - Ultimate Edition"
APP_VERSION = "7.0.0"
ICON_PATH = None


class PDBError(Exception):
    """PDB processing error"""
    pass


class Platform(Enum):
    WINDOWS = "windows"
    MACOS = "macos"
    LINUX = "linux"
    UNKNOWN = "unknown"


class PlatformHelper:
    _instance = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._initialized = False
        return cls._instance
    
    def __init__(self):
        if self._initialized:
            return
        self._initialized = True
        self._platform = self._detect_platform()
        logging.info(f"Platform detected: {self._platform.value}")
    
    @staticmethod
    def _detect_platform() -> Platform:
        if sys.platform.startswith('win'):
            return Platform.WINDOWS
        elif sys.platform == 'darwin':
            return Platform.MACOS
        elif sys.platform.startswith('linux'):
            return Platform.LINUX
        else:
            return Platform.UNKNOWN
    
    @property
    def platform(self) -> Platform:
        return self._platform
    
    @property
    def is_windows(self) -> bool:
        return self._platform == Platform.WINDOWS
    
    @property
    def is_macos(self) -> bool:
        return self._platform == Platform.MACOS
    
    @property
    def is_linux(self) -> bool:
        return self._platform == Platform.LINUX
    
    @property
    def is_unix(self) -> bool:
        return self._platform in (Platform.MACOS, Platform.LINUX)
    
    @property
    def executable_extension(self) -> str:
        return '.exe' if self.is_windows else ''
    
    @property
    def shell_script_extension(self) -> str:
        return '.bat' if self.is_windows else ''
    
    @property
    def temp_directory(self) -> Path:
        return Path(tempfile.gettempdir())
    
    @property
    def home_directory(self) -> Path:
        return Path.home()
    
    def get_documents_directory(self) -> Path:
        docs = self.home_directory / "Documents"
        docs.mkdir(parents=True, exist_ok=True)
        return docs
    
    def normalize_path(self, path: Union[str, Path]) -> Path:
        return Path(path).resolve()
    
    def path_to_string(self, path: Union[str, Path]) -> str:
        p = Path(path)
        if self.is_windows:
            return str(p).replace('/', '\\')
        else:
            return str(p).replace('\\', '/')


class JavaFinder:
    def __init__(self):
        self.platform_helper = PlatformHelper()
        self._cached_java_path: Optional[Path] = None
    
    def find_java(self) -> Optional[Path]:
        if self._cached_java_path and self._cached_java_path.exists():
            return self._cached_java_path
        
        java_path = None
        
        if self.platform_helper.is_windows:
            java_path = self._find_java_windows()
        elif self.platform_helper.is_macos:
            java_path = self._find_java_macos()
        elif self.platform_helper.is_linux:
            java_path = self._find_java_linux()
        
        if java_path:
            self._cached_java_path = java_path
            logging.info(f"Java found at: {java_path}")
        else:
            logging.warning("Java not found on system")
        
        return java_path
    
    def _find_java_windows(self) -> Optional[Path]:
        path_java = shutil.which("java")
        if path_java:
            java_path = Path(path_java)
            if java_path.exists():
                return java_path
        
        java_home = os.environ.get('JAVA_HOME')
        if java_home:
            java_exe = Path(java_home) / "bin" / "java.exe"
            if java_exe.exists():
                return java_exe
        
        common_paths = [
            Path(r"C:\Program Files\Eclipse Adoptium"),
            Path(r"C:\Program Files\Java"),
            Path(r"C:\Program Files (x86)\Java"),
        ]
        
        for base_path in common_paths:
            java_exe = self._search_java_in_directory_windows(base_path)
            if java_exe:
                return java_exe
        
        return None
    
    def _search_java_in_directory_windows(self, base_dir: Path) -> Optional[Path]:
        if not base_dir.exists():
            return None
        
        direct_java = base_dir / "bin" / "java.exe"
        if direct_java.exists():
            return direct_java
        
        try:
            for item in base_dir.iterdir():
                if item.is_dir():
                    java_exe = item / "bin" / "java.exe"
                    if java_exe.exists():
                        return java_exe
        except PermissionError:
            pass
        
        return None
    
    def _find_java_macos(self) -> Optional[Path]:
        try:
            result = subprocess.run(
                ['/usr/libexec/java_home'],
                capture_output=True,
                text=True,
                timeout=5
            )
            if result.returncode == 0:
                java_home = Path(result.stdout.strip())
                java_exe = java_home / "bin" / "java"
                if java_exe.exists():
                    return java_exe
        except (subprocess.TimeoutExpired, FileNotFoundError):
            pass
        
        path_java = shutil.which("java")
        if path_java:
            java_path = Path(path_java).resolve()
            if java_path.exists():
                return java_path
        
        return None
    
    def _find_java_linux(self) -> Optional[Path]:
        path_java = shutil.which("java")
        if path_java:
            java_path = Path(path_java).resolve()
            if java_path.exists():
                return java_path
        
        java_home = os.environ.get('JAVA_HOME')
        if java_home:
            java_exe = Path(java_home) / "bin" / "java"
            if java_exe.exists():
                return java_exe
        
        common_paths = [
            Path("/usr/bin/java"),
            Path("/usr/lib/jvm"),
        ]
        
        for path in common_paths:
            if path.is_file() and path.exists():
                return path
        
        return None
    
    def get_java_home(self) -> Optional[Path]:
        java_path = self.find_java()
        if java_path:
            return java_path.parent.parent
        return None


class OrthostericAutoDetector:
    """Auto-detects orthosteric region when user doesn't provide a file."""
    
    def __init__(self, main_structure, main_structure_path: str):
        self.main_structure = main_structure
        self.main_structure_path = main_structure_path
    
    def detect_orthosteric_region(self) -> Tuple[Optional[Structure], set]:
        logging.info("Orthosteric region not provided. Attempting auto-detection...")
        
        try:
            residues = self._calculate_geometric_region()
            if residues:
                logging.info(f"Geometric: Found {len(residues)} orthosteric residues")
                return None, residues
        except Exception as e:
            logging.warning(f"Geometric calculation failed: {e}")
        
        logging.error("Auto-detection failed. Using empty orthosteric region.")
        return None, set()
    
    def _extract_pdb_id(self) -> Optional[str]:
        filename = Path(self.main_structure_path).name
        match = re.search(r'(?:pdb)?([0-9][a-z0-9]{3})', filename, re.IGNORECASE)
        if match:
            return match.group(1).lower()
        return None
    
    def _calculate_geometric_region(self, cutoff: float = 5.0) -> set:
        EXCLUDED_HETEROATOMS = {'HOH', 'WAT', 'NA', 'CL', 'CA', 'MG', 'K', 
                                'ZN', 'FE', 'MN', 'CU', 'CD', 'NI', 'CO'}
        
        ligands = []
        
        for model in self.main_structure:
            for chain in model:
                for residue in chain:
                    hetflag = residue.get_id()[0]
                    resname = residue.get_resname().strip().upper()
                    
                    if hetflag.startswith('H_') or (hetflag != ' ' and resname not in EXCLUDED_HETEROATOMS):
                        if resname not in EXCLUDED_HETEROATOMS:
                            atom_count = len(list(residue.get_atoms()))
                            if atom_count >= 5:
                                ligands.append((residue, atom_count, chain.id))
        
        if not ligands:
            raise Exception("No ligands found in structure")
        
        ligands.sort(key=lambda x: x[1], reverse=True)
        largest_ligand, _, ligand_chain = ligands[0]
        
        logging.info(f"Largest ligand: {largest_ligand.get_resname()} "
                    f"(chain {ligand_chain}, {ligands[0][1]} atoms)")
        
        protein_coords = []
        coord_to_residue = {}
        
        for model in self.main_structure:
            for chain in model:
                chain_id = chain.id.strip() if chain.id.strip() else ' '
                for residue in chain:
                    if residue.get_id()[0] == ' ':
                        resid = int(residue.get_id()[1])
                        for atom in residue:
                            idx = len(protein_coords)
                            protein_coords.append(atom.coord)
                            coord_to_residue[idx] = (chain_id, resid)
        
        if not protein_coords:
            raise Exception("No protein atoms found")
        
        tree = cKDTree(np.array(protein_coords))
        
        nearby_residues = set()
        for atom in largest_ligand.get_atoms():
            indices = tree.query_ball_point(atom.coord, cutoff)
            for idx in indices:
                if idx in coord_to_residue:
                    nearby_residues.add(coord_to_residue[idx])
        
        return nearby_residues


class ValidationDataManager:
    """Manages all data files required for validation (Ligand-free version)."""
    
    def __init__(self):
        self.platform_helper = PlatformHelper()
        self.main_structure = None
        self.main_structure_path = None
        self.allosteric_structure = None
        self.allosteric_residues = set()
        self.orthosteric_structure = None
        self.orthosteric_residues = set()
        self.predicted_hubs = set()
        self.universe_residues = set()
    
    def _get_temp_path(self, suffix: str = ".pdb") -> Path:
        return self.platform_helper.temp_directory / f"temp_structure{suffix}"
    
    def load_main_structure(self, filepath: str):
        filepath = Path(filepath)
        if not filepath.exists():
            raise FileNotFoundError(f"Main structure file not found: {filepath}")
        
        self.main_structure_path = str(filepath)
        ext = filepath.suffix.lower()
        
        if ext == '.cif':
            parser = MMCIFParser(QUIET=True)
        elif ext == '.pdb' or str(filepath).endswith('.pdb.gz'):
            parser = PDBParser(QUIET=True)
        else:
            raise ValueError(f"Unsupported file format: {ext}")
        
        if str(filepath).endswith('.gz'):
            temp_path = self._get_temp_path()
            with gzip.open(filepath, 'rt') as f:
                temp_path.write_text(f.read())
            self.main_structure = parser.get_structure('main', str(temp_path))
            temp_path.unlink()
        else:
            self.main_structure = parser.get_structure('main', str(filepath))
        
        self.universe_residues = self._extract_residues_from_structure(self.main_structure)
        return len(self.universe_residues)
    
    def load_allosteric(self, filepath: str):
        self.allosteric_structure, self.allosteric_residues = self._load_region_file(filepath)
        return len(self.allosteric_residues)
    
    def load_orthosteric(self, filepath: str):
        self.orthosteric_structure, self.orthosteric_residues = self._load_region_file(filepath)
        return len(self.orthosteric_residues)
    
    def auto_detect_orthosteric(self) -> int:
        if not self.main_structure:
            raise ValueError("Main structure must be loaded first")
        
        detector = OrthostericAutoDetector(self.main_structure, self.main_structure_path)
        self.orthosteric_structure, self.orthosteric_residues = detector.detect_orthosteric_region()
        return len(self.orthosteric_residues)
    
    def _load_region_file(self, filepath: str):
        filepath = Path(filepath)
        if not filepath.exists():
            raise FileNotFoundError(f"Region file not found: {filepath}")
        
        parser = PDBParser(QUIET=True)
        
        if str(filepath).endswith('.gz'):
            temp_path = self._get_temp_path('.pdb')
            with gzip.open(filepath, 'rt') as f:
                temp_path.write_text(f.read())
            structure = parser.get_structure('region', str(temp_path))
            temp_path.unlink()
        else:
            structure = parser.get_structure('region', str(filepath))
        
        residues = self._extract_residues_from_structure(structure)
        return structure, residues
    
    def _extract_residues_from_structure(self, structure) -> set:
        residues = set()
        for model in structure:
            for chain in model:
                chain_id = chain.id.strip() if chain.id.strip() else ' '
                for residue in chain:
                    if residue.get_id()[0] == ' ':
                        resid = int(residue.get_id()[1])
                        residues.add((chain_id, resid))
        return residues
    
    def load_predicted_hubs_from_top5(self, filepath: str):
        filepath = Path(filepath)
        if not filepath.exists():
            raise FileNotFoundError(f"Top 5% file not found: {filepath}")
        
        self.predicted_hubs = set()
        
        with open(filepath, 'r') as f:
            for line_num, line in enumerate(f):
                line = line.strip()
                
                if not line or line_num == 0 or line.startswith('i_resSeq'):
                    continue
                
                parts = line.split()
                
                if len(parts) >= 3:
                    try:
                        resid = int(parts[0])
                        chain = parts[2].strip()
                        self.predicted_hubs.add((chain, resid))
                    except (ValueError, IndexError):
                        logging.warning(f"Could not parse line {line_num}: {line}")
                        continue
        
        logging.info(f"Loaded {len(self.predicted_hubs)} predicted hubs from {filepath}")
        return len(self.predicted_hubs)
    
    def get_universe_residues(self) -> set:
        return self.universe_residues.copy()


class ProximityCalculator:
    """Calculates proximity-based neighbors using KD-Tree."""
    
    def __init__(self, structure):
        self.structure = structure
        self.kdtree = None
        self.atom_lookup = {}
        self._build_spatial_index()
    
    def _build_spatial_index(self):
        coords = []
        
        for model in self.structure:
            for chain in model:
                chain_id = chain.id.strip() if chain.id.strip() else ' '
                for residue in chain:
                    if residue.get_id()[0] == ' ':
                        resid = int(residue.get_id()[1])
                        for atom in residue:
                            idx = len(coords)
                            coords.append(atom.coord)
                            self.atom_lookup[idx] = (chain_id, resid)
        
        if coords:
            self.kdtree = cKDTree(np.array(coords))
    
    def get_neighbors_within_distance(self, residue_list: set, cutoff: float = 5.0) -> set:
        if not self.kdtree or not residue_list:
            return set()
        
        neighbors = set(residue_list)
        
        for chain, resid in residue_list:
            residue_atom_indices = [
                idx for idx, (c, r) in self.atom_lookup.items()
                if c == chain and r == resid
            ]
            
            for atom_idx in residue_atom_indices:
                atom_coord = self.kdtree.data[atom_idx]
                nearby_indices = self.kdtree.query_ball_point(atom_coord, cutoff)
                
                for nearby_idx in nearby_indices:
                    if nearby_idx in self.atom_lookup:
                        neighbors.add(self.atom_lookup[nearby_idx])
        
        return neighbors


class TruePositiveSetBuilder:
    """Builds the True Positive sets using the 5A proximity rule (Ligand-free version)."""
    
    def __init__(self, proximity_calc: ProximityCalculator):
        self.prox_calc = proximity_calc
    
    def build_T_Allo(self, allosteric_residues: set) -> set:
        return self.prox_calc.get_neighbors_within_distance(allosteric_residues, 5.0)
    
    def build_T_Orto(self, orthosteric_residues: set) -> set:
        return self.prox_calc.get_neighbors_within_distance(orthosteric_residues, 5.0)


class ConfusionMatrixCalculator:
    """Calculates confusion matrix and performance metrics."""
    
    def __init__(self, universe_residues: set):
        self.universe = universe_residues
    
    def calculate(self, P: set, T: set) -> dict:
        tp_residues_set = P & T
        fp_residues_set = P - T
        fn_residues_set = T - P
        tn_residues_set = self.universe - (P | T)
        
        TP = len(tp_residues_set)
        FP = len(fp_residues_set)
        FN = len(fn_residues_set)
        TN = len(tn_residues_set)
        
        total = TP + FP + FN + TN
        universe_size = len(self.universe)
        
        if total != universe_size:
            logging.warning(f"Universe mismatch! TP+FP+FN+TN={total} != Universe={universe_size}")
        
        precision = TP / (TP + FP) if (TP + FP) > 0 else 0.0
        recall = TP / (TP + FN) if (TP + FN) > 0 else 0.0
        f1_score = (2 * precision * recall) / (precision + recall) if (precision + recall) > 0 else 0.0
        accuracy = (TP + TN) / universe_size if universe_size > 0 else 0.0
        specificity = TN / (TN + FP) if (TN + FP) > 0 else 0.0
        
        tp_residues = sorted(list(tp_residues_set))
        fp_residues = sorted(list(fp_residues_set))
        fn_residues = sorted(list(fn_residues_set))
        
        return {
            'TP': TP, 'FP': FP, 'FN': FN, 'TN': TN,
            'precision': precision, 'recall': recall, 'f1_score': f1_score,
            'accuracy': accuracy, 'specificity': specificity,
            'tp_residues': tp_residues, 'fp_residues': fp_residues,
            'fn_residues': fn_residues, 'total': total, 'universe_size': universe_size
        }


class ValidationThread(QThread):
    """Runs validation analysis in background thread (Ligand-free version)"""
    
    progress_update = Signal(int, str)
    validation_complete = Signal(dict)
    error_occurred = Signal(str)
    
    def __init__(self, main_structure_path: str, allosteric_path: str, orthosteric_path: str, top5_path: str):
        super().__init__()
        self.main_structure_path = main_structure_path
        self.allosteric_path = allosteric_path
        self.orthosteric_path = orthosteric_path
        self.top5_path = top5_path
        self.is_running = True
    
    def run(self):
        try:
            self.progress_update.emit(10, "Loading main structure...")
            data_manager = ValidationDataManager()
            
            universe_count = data_manager.load_main_structure(self.main_structure_path)
            self.progress_update.emit(15, f"Universe: {universe_count} residues")
            
            self.progress_update.emit(20, "Loading allosteric region...")
            allo_count = data_manager.load_allosteric(self.allosteric_path)
            
            self.progress_update.emit(30, "Loading/detecting orthosteric region...")
            if self.orthosteric_path and Path(self.orthosteric_path).exists():
                orto_count = data_manager.load_orthosteric(self.orthosteric_path)
                orto_source = "user_file"
            else:
                self.progress_update.emit(35, "Auto-detecting orthosteric region...")
                orto_count = data_manager.auto_detect_orthosteric()
                orto_source = "auto_detected"
            
            self.progress_update.emit(40, "Loading predicted hubs...")
            hub_count = data_manager.load_predicted_hubs_from_top5(self.top5_path)
            
            self.progress_update.emit(50, "Building spatial index...")
            prox_calc = ProximityCalculator(data_manager.main_structure)
            builder = TruePositiveSetBuilder(prox_calc)
            
            self.progress_update.emit(60, "Calculating zones...")
            T_Allo_Core = data_manager.allosteric_residues.copy()
            T_Allo_5A = builder.build_T_Allo(data_manager.allosteric_residues)
            T_Orto_Core = data_manager.orthosteric_residues.copy()
            T_Orto_5A = builder.build_T_Orto(data_manager.orthosteric_residues)
            
            # Shell = 5A zone minus core
            T_Allo_Shell = T_Allo_5A - T_Allo_Core
            T_Orto_Shell = T_Orto_5A - T_Orto_Core
            
            self.progress_update.emit(80, "Computing confusion matrices...")
            cm_calc = ConfusionMatrixCalculator(data_manager.universe_residues)
            
            results_allo_core = cm_calc.calculate(data_manager.predicted_hubs, T_Allo_Core)
            results_allo_5a = cm_calc.calculate(data_manager.predicted_hubs, T_Allo_5A)
            results_orto_core = cm_calc.calculate(data_manager.predicted_hubs, T_Orto_Core)
            results_orto_5a = cm_calc.calculate(data_manager.predicted_hubs, T_Orto_5A)
            
            all_results = {
                'allo_core': results_allo_core, 'allo_5a': results_allo_5a,
                'orto_core': results_orto_core, 'orto_5a': results_orto_5a,
                'metadata': {
                    'universe_count': universe_count, 'allo_core_count': allo_count,
                    'orto_core_count': orto_count, 'orto_source': orto_source,
                    'hub_count': hub_count,
                    'T_Allo_Core_count': len(T_Allo_Core), 'T_Allo_5A_count': len(T_Allo_5A),
                    'T_Allo_Shell_count': len(T_Allo_Shell),
                    'T_Orto_Core_count': len(T_Orto_Core), 'T_Orto_5A_count': len(T_Orto_5A),
                    'T_Orto_Shell_count': len(T_Orto_Shell),
                    'allo_file': self.allosteric_path, 'orto_file': self.orthosteric_path
                },
                'zone_data': {
                    'T_Allo_Core': sorted(list(T_Allo_Core)), 'T_Allo_5A': sorted(list(T_Allo_5A)),
                    'T_Allo_Shell': sorted(list(T_Allo_Shell)),
                    'T_Orto_Core': sorted(list(T_Orto_Core)), 'T_Orto_5A': sorted(list(T_Orto_5A)),
                    'T_Orto_Shell': sorted(list(T_Orto_Shell)),
                    'predicted_hubs': sorted(list(data_manager.predicted_hubs))
                }
            }
            
            self.progress_update.emit(100, "Validation complete!")
            self.validation_complete.emit(all_results)
            
        except Exception as e:
            self.error_occurred.emit(f"Validation error: {str(e)}\n{traceback.format_exc()}")
    
    def stop(self):
        self.is_running = False


class AnalysisThread(QThread):
    """Runs the RIN analysis in a background thread with full Plotly visualizations."""
    
    progress_update = Signal(int, str)
    analysis_complete = Signal(dict)
    error_occurred = Signal(str)
    single_pdb_complete = Signal(str, dict)
    
    def __init__(self, pdb_files: List[str], output_dir: str, cutoff: float, top_percentile: float):
        super().__init__()
        self.pdb_files = pdb_files
        self.output_dir = output_dir
        self.cutoff = cutoff
        self.top_percentile = top_percentile
        self.is_running = True
        
    def run(self):
        try:
            all_results = {}
            total_files = len(self.pdb_files)
            
            for idx, pdb_path in enumerate(self.pdb_files):
                if not self.is_running:
                    break
                    
                progress_percent = int((idx / total_files) * 100)
                filename = Path(pdb_path).name
                self.progress_update.emit(progress_percent, f"Processing: {filename} ({idx+1}/{total_files})")
                
                pdb_id = self.extract_pdb_id(filename)
                protein_output_dir = Path(self.output_dir) / f"{pdb_id}_ALL"
                protein_output_dir.mkdir(parents=True, exist_ok=True)
                
                try:
                    results = self.analyze_single_pdb(pdb_path, pdb_id, str(protein_output_dir))
                    all_results[pdb_id] = results
                    self.single_pdb_complete.emit(pdb_id, results)
                except Exception as e:
                    error_msg = f"{pdb_id} analysis failed: {str(e)}"
                    self.error_occurred.emit(error_msg)
                    all_results[pdb_id] = {"error": error_msg, "pdb_id": pdb_id}
            
            self.progress_update.emit(100, "Analysis complete!")
            self.analysis_complete.emit(all_results)
            
        except Exception as e:
            self.error_occurred.emit(f"Critical error: {str(e)}")
    
    def stop(self):
        self.is_running = False
    
    def extract_pdb_id(self, filename: str) -> str:
        pdb_id_match = re.match(r'(pdb)?([a-zA-Z0-9]{4})', filename, re.IGNORECASE)
        if pdb_id_match:
            return pdb_id_match.group(2).upper()
        return Path(filename).stem.split('.')[0].upper()
    
    def analyze_single_pdb(self, pdb_path: str, pdb_id: str, output_dir: str) -> dict:
        results = {"pdb_id": pdb_id, "output_dir": output_dir, "status": "processing"}
        
        try:
            structure, _, fortran_data = self.pre_processor_and_data_preparation(pdb_path, pdb_id)
            connectivity_data, centroid_coords, residue_map = self.calculate_affinity_and_centroids(fortran_data, output_dir)
            hub_orig_seq_nums = self.network_analyzer_and_visualizer(connectivity_data, centroid_coords, residue_map, output_dir, pdb_id)
            self.post_process_and_report_simple(hub_orig_seq_nums, output_dir)
            
            results["status"] = "completed"
            results["hub_residues"] = hub_orig_seq_nums
            results["num_residues"] = len(residue_map)
            results["num_contacts"] = len(connectivity_data) if connectivity_data else 0
            
            abs_output_dir = Path(output_dir).resolve()
            results["files"] = {
                "connectivity": str(abs_output_dir / "connectivity.out"),
                "betweenness": str(abs_output_dir / "betweenness.out"),
                "top5": str(abs_output_dir / "top_5_percent.out"),
                "hubs": str(abs_output_dir / "predicted_hubs.txt"),
                "plot_2d_cb_vs_residue": str(abs_output_dir / "plot_2D_CB_vs_Residue.html"),
                "plot_2d_cb_histogram": str(abs_output_dir / "plot_2D_CB_Histogram.html"),
                "plot_3d_network_cb": str(abs_output_dir / "plot_3D_Network_CB.html"),
                "plot_3d_network_spectral": str(abs_output_dir / "plot_3D_Network_Spectral.html"),
                "10modes": str(abs_output_dir / "10modes.txt"),
                "10modes_normalized": str(abs_output_dir / "10modes_normalized.txt")
            }
        except Exception as e:
            results["status"] = "error"
            results["error"] = str(e)
        
        return results
    
    def pre_processor_and_data_preparation(self, pdb_path: str, pdb_id: str) -> Tuple:
        pdb_path = Path(pdb_path)
        if not pdb_path.exists():
            raise PDBError(f"PDB file not found: {pdb_path}")
        
        parser = MMCIFParser(QUIET=True) if pdb_path.suffix.lower() == '.cif' else PDBParser(QUIET=True)
        structure = parser.get_structure(pdb_id, str(pdb_path))
        
        atom_list, atom_coords, residue_map, residue_atom_counts = [], [], {}, {}
        res_counter = 0
        
        if 0 not in structure:
            raise PDBError("Model 0 not found")
        
        for chain in structure[0]:
            chain_id_str = chain.id.strip() if chain.id.strip() else ' '
            for residue in chain:
                if residue.get_id()[0] == ' ' and residue.get_id()[2] == ' ':
                    res_counter += 1
                    residue_map[res_counter] = {
                        "res_seq": residue.get_id()[1], "res_name": residue.get_resname().strip(),
                        "chain_id": chain_id_str, "internal_idx": res_counter
                    }
                    current_count = 0
                    for atom in residue:
                        alt_loc = atom.get_altloc()
                        if alt_loc == ' ' or alt_loc == 'A':
                            atom_list.append(atom)
                            atom_coords.append(atom.get_coord())
                            current_count += 1
                    residue_atom_counts[res_counter] = current_count
        
        if not residue_map:
            raise PDBError("No valid residues found")
        
        rno = res_counter
        nresidue = len(atom_list)
        if nresidue == 0:
            raise PDBError("No valid atoms found")
        
        all_atom_coords = np.array(atom_coords)
        atom_to_residue_map = np.zeros(nresidue, dtype=int)
        current_atom_idx = 0
        
        for res_idx in range(1, rno + 1):
            count = residue_atom_counts.get(res_idx, 0)
            if count > 0 and current_atom_idx + count <= nresidue:
                atom_to_residue_map[current_atom_idx:current_atom_idx + count] = res_idx
                current_atom_idx += count
        
        fortran_data = {
            "rno": rno, "nresidue": nresidue, "all_atom_coords": all_atom_coords,
            "residue_map": residue_map, "residue_atom_counts": residue_atom_counts,
            "atom_to_residue_map": atom_to_residue_map
        }
        
        return structure, str(pdb_path), fortran_data
    
    def calculate_affinity_and_centroids(self, fortran_data: dict, output_dir: str) -> Tuple:
        rno = fortran_data["rno"]
        all_atom_coords = fortran_data["all_atom_coords"]
        residue_map = fortran_data["residue_map"]
        residue_atom_counts = fortran_data["residue_atom_counts"]
        atom_to_residue_map = fortran_data["atom_to_residue_map"]
        
        centroid_coords = np.zeros((rno, 3))
        for res_idx in range(1, rno + 1):
            atom_mask = (atom_to_residue_map == res_idx)
            if np.sum(atom_mask) > 0:
                centroid_coords[res_idx - 1] = np.mean(all_atom_coords[atom_mask], axis=0)
        
        tree = cKDTree(all_atom_coords)
        pairs_within_cutoff = tree.query_pairs(r=self.cutoff, output_type='ndarray')
        
        contact_counts = defaultdict(int)
        for atom_i, atom_j in pairs_within_cutoff:
            res_i, res_j = atom_to_residue_map[atom_i], atom_to_residue_map[atom_j]
            if res_i != res_j and res_i > 0 and res_j > 0:
                contact_counts[(min(res_i, res_j), max(res_i, res_j))] += 1
        
        connectivity_data = []
        for (res_i, res_j), Nij in contact_counts.items():
            Ni, Nj = residue_atom_counts.get(res_i, 1), residue_atom_counts.get(res_j, 1)
            aij = Nij / (math.sqrt(Ni) * math.sqrt(Nj))
            edge_weight = 1.0 / aij if aij > 0 else float('inf')
            connectivity_data.append({'res_i': res_i, 'res_j': res_j, 'aij': aij, 'weight': edge_weight})
        
        output_dir = Path(output_dir)
        with open(output_dir / "connectivity.out", "w") as f:
            for conn in connectivity_data:
                f.write(f"{conn['res_i']:12d}{conn['res_j']:12d}  {conn['aij']:.8f}    \n")
        
        return connectivity_data, centroid_coords, residue_map
    
    def network_analyzer_and_visualizer(self, connectivity_data: List, centroid_coords: np.ndarray,
                                         residue_map: Dict, output_dir: str, pdb_id: str) -> List:
        G = nx.Graph()
        for conn in connectivity_data:
            G.add_edge(conn['res_i'], conn['res_j'], weight=conn['weight'])
        for res_idx in residue_map.keys():
            if res_idx not in G:
                G.add_node(res_idx)
        
        betweenness_dict = nx.betweenness_centrality(G, weight='weight', normalized=False)
        n = len(G.nodes())
        normalization_factor = (n - 2) * (n - 1)
        for node in betweenness_dict:
            if normalization_factor > 0:
                betweenness_dict[node] = 2 * betweenness_dict[node] / normalization_factor
        
        output_dir = Path(output_dir)
        with open(output_dir / "betweenness.out", "w") as f:
            f.write("i resn ch  CB     \n")
            for res_idx in sorted(residue_map.keys()):
                cb_val = betweenness_dict.get(res_idx, 0.0)
                ch, seq = residue_map[res_idx]["chain_id"], residue_map[res_idx]["res_seq"]
                resname = residue_map[res_idx]["res_name"]
                f.write(f"{seq} {resname}  {ch}  {cb_val:.7f}\n")
        
        cb_values = list(betweenness_dict.values())
        threshold = np.quantile(cb_values, self.top_percentile)
        
        with open(output_dir / "top_5_percent.out", "w") as f:
            f.write("i resn ch  CB     \n")
            for res_idx in sorted(residue_map.keys()):
                cb_val = betweenness_dict.get(res_idx, 0.0)
                if cb_val >= threshold:
                    ch, seq = residue_map[res_idx]["chain_id"], residue_map[res_idx]["res_seq"]
                    resname = residue_map[res_idx]["res_name"]
                    f.write(f"{seq}  {resname}  {ch}  {cb_val:.7f}\n")
        
        hub_orig_seq_nums = [residue_map[res_idx]["res_seq"] for res_idx, cb_val in betweenness_dict.items() if cb_val >= threshold]
        
        fiedler_vector = self.spectral_analysis(G, residue_map, output_dir)
        self.create_plotly_2d_plots(betweenness_dict, residue_map, str(output_dir), pdb_id)
        self.create_plotly_3d_plots(G, betweenness_dict, centroid_coords, residue_map, str(output_dir), pdb_id, fiedler_vector)
        
        return hub_orig_seq_nums
    
    def spectral_analysis(self, G: nx.Graph, residue_map: dict, output_dir) -> np.ndarray:
        output_dir = Path(output_dir)
        L = nx.laplacian_matrix(G, weight='weight').toarray()
        n = L.shape[0]
        if n < 2:
            return np.zeros(n)
        
        eigenvalues, eigenvectors = scipy.linalg.eigh(L)
        num_modes = min(10, n - 1)
        modes = eigenvectors[:, 1:num_modes + 1]
        
        np.savetxt(str(output_dir / "10modes.txt"), modes, delimiter='\t', fmt='%.15g')
        
        nmod = np.zeros_like(modes)
        for i in range(modes.shape[1]):
            for j in range(modes.shape[0]):
                val = modes[j, i]
                nmod[j, i] = 1 if val > 0 else (-1 if val < 0 else 0)
        np.savetxt(str(output_dir / "10modes_normalized.txt"), nmod.astype(int), delimiter='\t', fmt='%d')
        
        return modes[:, 0] if modes.shape[1] > 0 else np.zeros(n)
    
    def create_plotly_2d_plots(self, betweenness_dict, residue_map, output_dir, pdb_id):
        residue_indices = sorted(residue_map.keys())
        cb_values = [betweenness_dict.get(idx, 0.0) for idx in residue_indices]
        
        fig1 = go.Figure()
        fig1.add_trace(go.Scatter(x=residue_indices, y=cb_values, mode='lines+markers',
                                   name='Betweenness Centrality', line=dict(color='royalblue', width=2), marker=dict(size=4)))
        fig1.update_layout(title=f"Betweenness Centrality - {pdb_id}", xaxis_title="Residue Index",
                          yaxis_title="Betweenness Centrality", template="plotly_white", hovermode='closest')
        fig1.write_html(str(Path(output_dir) / "plot_2D_CB_vs_Residue.html"))
        
        fig2 = go.Figure()
        fig2.add_trace(go.Histogram(x=cb_values, nbinsx=50, name='CB Distribution', marker=dict(color='indianred')))
        fig2.update_layout(title=f"Betweenness Centrality Distribution - {pdb_id}", xaxis_title="Betweenness Centrality",
                          yaxis_title="Count", template="plotly_white")
        fig2.write_html(str(Path(output_dir) / "plot_2D_CB_Histogram.html"))
    
    def create_plotly_3d_plots(self, G, betweenness_dict, centroid_coords, residue_map, output_dir, pdb_id, fiedler_vector=None):
        pos_3d = {res_idx: centroid_coords[res_idx - 1] for res_idx in residue_map.keys() if res_idx <= len(centroid_coords)}
        
        edge_trace = self._create_3d_edge_trace(G, pos_3d)
        node_trace = self._create_3d_node_trace(G, pos_3d, betweenness_dict, 'CB')
        
        fig1 = go.Figure(data=[edge_trace, node_trace])
        fig1.update_layout(title=f"3D Network (CB) - {pdb_id}", showlegend=False,
                          scene=dict(xaxis=dict(showbackground=False), yaxis=dict(showbackground=False), zaxis=dict(showbackground=False)))
        fig1.write_html(str(Path(output_dir) / "plot_3D_Network_CB.html"))
        
        if fiedler_vector is not None and len(fiedler_vector) > 0:
            node_list = sorted(residue_map.keys())
            node_x, node_y, node_z, node_colors, node_texts = [], [], [], [], []
            for i, res_idx in enumerate(node_list):
                if res_idx in pos_3d and i < len(fiedler_vector):
                    x, y, z = pos_3d[res_idx]
                    node_x.append(x); node_y.append(y); node_z.append(z)
                    node_colors.append('red' if fiedler_vector[i] >= 0 else 'blue')
                    node_texts.append(f"Res {res_idx}: Fiedler={fiedler_vector[i]:.4f}")
            
            node_trace_spectral = go.Scatter3d(x=node_x, y=node_y, z=node_z, mode='markers',
                                               marker=dict(size=6, color=node_colors, line=dict(width=1, color='white')),
                                               text=node_texts, hoverinfo='text')
            fig2 = go.Figure(data=[edge_trace, node_trace_spectral])
            fig2.update_layout(title=f"Spectral Partitioning (Fiedler Vector) - {pdb_id}<br>Red: ≥0, Blue: <0",
                              showlegend=False, scene=dict(xaxis=dict(showbackground=False), yaxis=dict(showbackground=False), zaxis=dict(showbackground=False)))
        else:
            node_trace_spectral = self._create_3d_node_trace(G, pos_3d, betweenness_dict, 'spectral')
            fig2 = go.Figure(data=[edge_trace, node_trace_spectral])
            fig2.update_layout(title=f"3D Network (Spectral) - {pdb_id}", showlegend=False,
                              scene=dict(xaxis=dict(showbackground=False), yaxis=dict(showbackground=False), zaxis=dict(showbackground=False)))
        
        fig2.write_html(str(Path(output_dir) / "plot_3D_Network_Spectral.html"))
    
    def _create_3d_edge_trace(self, G, pos_3d):
        edge_x, edge_y, edge_z = [], [], []
        for edge in G.edges():
            if edge[0] in pos_3d and edge[1] in pos_3d:
                x0, y0, z0 = pos_3d[edge[0]]
                x1, y1, z1 = pos_3d[edge[1]]
                edge_x.extend([x0, x1, None]); edge_y.extend([y0, y1, None]); edge_z.extend([z0, z1, None])
        return go.Scatter3d(x=edge_x, y=edge_y, z=edge_z, mode='lines', line=dict(color='gray', width=1), hoverinfo='none')
    
    def _create_3d_node_trace(self, G, pos_3d, betweenness_dict, colorscale_type):
        node_x, node_y, node_z, node_colors, node_texts = [], [], [], [], []
        for node in G.nodes():
            if node in pos_3d:
                x, y, z = pos_3d[node]
                node_x.append(x); node_y.append(y); node_z.append(z)
                node_colors.append(betweenness_dict.get(node, 0.0))
                node_texts.append(f"Node {node}")
        colorscale = 'Viridis' if colorscale_type == 'CB' else 'Spectral'
        return go.Scatter3d(x=node_x, y=node_y, z=node_z, mode='markers',
                           marker=dict(size=5, color=node_colors, colorscale=colorscale, showscale=True, colorbar=dict(title="Betweenness")),
                           text=node_texts, hoverinfo='text')
    
    def post_process_and_report_simple(self, hub_orig_seq_nums: List, output_dir: str):
        with open(Path(output_dir) / "predicted_hubs.txt", "w") as f:
            f.write("+".join(map(str, sorted(hub_orig_seq_nums))))


class PocketTool(Enum):
    P2RANK = "p2rank"
    FPOCKET = "fpocket"


@dataclass
class PocketDetectionConfig:
    """
    Pocket detection configuration with DISCOVERY MODE parameters.
    
    Discovery Mode Philosophy:
    - Hub residues are the PRIMARY indicator of druggability
    - Validation zones confirm known sites
    - The JACKPOT: High-hub pockets with NO validation overlap = NOVEL candidates
    """
    tool: PocketTool = PocketTool.P2RANK
    tool_path: str = ""
    p2rank_model: str = "default"
    fpocket_min_alpha_spheres: int = 35
    min_pocket_score: float = 0.0
    max_pockets: int = 20
    
    # Base weights (sum should equal ~1.0 for interpretability)
    weight_geometric: float = 0.30      # Reduced: geometry alone isn't enough
    weight_hub_impact: float = 0.50     # INCREASED: hubs are the key signal
    weight_validation: float = 0.20     # Confirmation bonus
    
    # Hub Impact Parameters (non-linear scaling)
    hub_impact_base: float = 1.5        # Base multiplier per hub
    hub_impact_saturation: int = 5      # Diminishing returns after N hubs
    min_hubs_for_candidate: int = 1     # Minimum hubs to be considered "druggable"
    
    # Discovery Mode Bonuses
    novelty_bonus: float = 0.25         # Bonus for NOVEL_CANDIDATE (no validation overlap)
    confirmation_bonus: float = 0.15    # Bonus for CONFIRMED_SITE (has validation overlap)
    
    # Penalty for hubless pockets
    no_hub_penalty: float = 0.6         # Multiplier for pockets with 0 hubs (60% of score)
    
    # Legacy parameters (kept for backward compatibility)
    boost_allosteric: float = 0.50
    boost_orthosteric: float = 0.50


@dataclass
class DetectedPocket:
    """
    Detected pocket data with DISCOVERY MODE scoring.
    
    Categories (Priority Order):
    1. NOVEL_CANDIDATE: Has hubs, NO validation overlap → Potential new drug target!
    2. CONFIRMED_SITE: Has hubs, overlaps validation → Known functional site
    3. CRYPTIC_POCKET: Good geometry, but no hubs → Might open upon binding
    4. LOW_PRIORITY: Poor geometry and no hubs
    """
    pocket_id: int
    name: str
    residues: Set[Tuple[str, int]]
    center: np.ndarray
    volume: float = 0.0
    raw_score: float = 0.0
    probability: float = 0.0
    
    # Hub Analysis
    hub_density: float = 0.0
    hub_count: int = 0
    hubs_in_pocket: List[Tuple[str, int]] = field(default_factory=list)
    
    # Validation Overlap
    overlaps_allosteric: bool = False
    overlaps_orthosteric: bool = False
    allo_overlap_count: int = 0
    orto_overlap_count: int = 0
    
    # Score Components (Legacy + New)
    geometric_score_normalized: float = 0.0
    hub_density_score: float = 0.0
    validation_boost: float = 0.0
    
    # NEW: Discovery Mode Scores
    hub_impact_factor: float = 0.0      # Non-linear hub contribution
    novelty_bonus: float = 0.0          # Bonus for NOVEL_CANDIDATE
    discovery_category: str = ""        # NOVEL_CANDIDATE, CONFIRMED_SITE, CRYPTIC_POCKET, LOW_PRIORITY
    category_priority: int = 99         # Lower = better (for sorting)
    
    # Final Score
    consensus_score: float = 0.0
    validation_tags: List[str] = field(default_factory=list)
    
    def __post_init__(self):
        if isinstance(self.residues, list):
            self.residues = set(self.residues)


class P2RankRunner:
    """Cross-platform wrapper for P2Rank pocket detection tool."""
    
    def __init__(self, p2rank_path: str, model: str = "default"):
        self.p2rank_path = Path(p2rank_path)
        self.model = model
        self.platform_helper = PlatformHelper()
        self.java_finder = JavaFinder()
        self.p2rank_script: Optional[Path] = None
        self._validate_installation()
    
    def _validate_installation(self):
        if not self.p2rank_path:
            raise ValueError("P2Rank path not specified")
        if self.p2rank_path.is_dir():
            self._find_p2rank_script_in_directory()
        elif self.p2rank_path.is_file():
            self.p2rank_script = self.p2rank_path
        else:
            raise FileNotFoundError(f"P2Rank not found at {self.p2rank_path}")
    
    def _find_p2rank_script_in_directory(self):
        script_names = ["prank.bat", "prank.cmd"] if self.platform_helper.is_windows else ["prank", "prank.sh"]
        for location in [self.p2rank_path, self.p2rank_path / "bin"]:
            for script_name in script_names:
                script_path = location / script_name
                if script_path.exists():
                    self.p2rank_script = script_path
                    if self.platform_helper.is_unix:
                        self._ensure_executable(script_path)
                    return
        raise FileNotFoundError(f"P2Rank script not found in {self.p2rank_path}")
    
    def _ensure_executable(self, script_path: Path):
        if self.platform_helper.is_unix:
            try:
                script_path.chmod(script_path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
            except Exception as e:
                logging.warning(f"Could not set executable permission: {e}")
    
    def _find_p2rank_jar(self) -> Optional[Path]:
        p2rank_dir = self.p2rank_script.parent if self.p2rank_script else self.p2rank_path
        for jar_path in [p2rank_dir / "bin" / "p2rank.jar", p2rank_dir / "p2rank.jar", p2rank_dir.parent / "bin" / "p2rank.jar"]:
            if jar_path.exists():
                return jar_path
        for search_dir in [p2rank_dir, p2rank_dir.parent]:
            if search_dir.exists():
                for jar_file in search_dir.rglob("*p2rank*.jar"):
                    return jar_file
        return None
    
    def run(self, pdb_path: str, output_dir: str) -> List[DetectedPocket]:
        pdb_path, output_dir = Path(pdb_path).resolve(), Path(output_dir).resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
        p2rank_dir = self.p2rank_script.parent if self.p2rank_script else self.p2rank_path
        
        java_path = self.java_finder.find_java()
        p2rank_jar = self._find_p2rank_jar()
        
        result = None
        if p2rank_jar and java_path:
            try:
                cmd = [str(java_path), "-Xmx4G", "-jar", str(p2rank_jar), "predict", "-f", str(pdb_path), "-o", str(output_dir)]
                result = subprocess.run(cmd, capture_output=True, text=True, cwd=str(p2rank_dir), timeout=600)
            except Exception as e:
                logging.warning(f"Direct Java execution failed: {e}")
        
        if result is None or result.returncode != 0:
            if self.p2rank_script:
                env = os.environ.copy()
                if java_path:
                    env['JAVA_HOME'] = str(java_path.parent.parent)
                cmd = [str(self.p2rank_script)] if self.platform_helper.is_windows else ['bash', str(self.p2rank_script)]
                cmd.extend(["predict", "-f", str(pdb_path), "-o", str(output_dir)])
                try:
                    result = subprocess.run(cmd, capture_output=True, text=True, cwd=str(p2rank_dir), env=env, timeout=600)
                except Exception as e:
                    logging.warning(f"Script execution failed: {e}")
        
        if result is None or result.returncode != 0:
            raise RuntimeError("P2Rank execution failed")
        
        return self._parse_results(str(output_dir), str(pdb_path))
    
    def _parse_results(self, output_dir: str, pdb_path: str) -> List[DetectedPocket]:
        pockets = []
        output_dir, pdb_name = Path(output_dir), Path(pdb_path).stem
        
        predictions_file = None
        for pattern in [output_dir / f"{pdb_name}.pdb_predictions.csv", output_dir / f"{pdb_name}_predictions.csv", output_dir / "predictions.csv"]:
            if pattern.exists():
                predictions_file = pattern
                break
        if not predictions_file:
            for csv_file in output_dir.rglob("*predictions*.csv"):
                predictions_file = csv_file
                break
        
        if not predictions_file or not predictions_file.exists():
            return pockets
        
        try:
            df = pd.read_csv(predictions_file, skipinitialspace=True)
            df.columns = df.columns.str.strip()
            
            for _, row in df.iterrows():
                rank = row.get('rank', row.name + 1)
                residues = set()
                residue_str = str(row.get('residue_ids', row.get('residues', '')))
                if residue_str and residue_str != 'nan':
                    for res in residue_str.split():
                        parts = res.replace('_', ':').split(':')
                        if len(parts) >= 2:
                            chain = parts[0] if parts[0] else 'A'
                            try:
                                residues.add((chain, int(parts[1])))
                            except ValueError:
                                continue
                
                center = np.array([float(row.get('center_x', 0)), float(row.get('center_y', 0)), float(row.get('center_z', 0))])
                pockets.append(DetectedPocket(pocket_id=int(rank), name=f"pocket_{int(rank)}", residues=residues, center=center,
                                             raw_score=float(row.get('score', 0)), probability=float(row.get('probability', 0))))
        except Exception as e:
            logging.error(f"Failed to parse P2Rank predictions: {e}")
        
        return pockets


class FpocketRunner:
    """Cross-platform wrapper for fpocket pocket detection tool."""
    
    def __init__(self, fpocket_path: str, min_alpha_spheres: int = 35):
        self.fpocket_path = Path(fpocket_path)
        self.min_alpha_spheres = min_alpha_spheres
        self.platform_helper = PlatformHelper()
        self._validate_installation()
    
    def _validate_installation(self):
        if not self.fpocket_path or not self.fpocket_path.exists():
            raise FileNotFoundError(f"fpocket not found at {self.fpocket_path}")
        if self.platform_helper.is_unix and self.fpocket_path.is_file():
            try:
                self.fpocket_path.chmod(self.fpocket_path.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
            except Exception as e:
                logging.warning(f"Could not set executable permission: {e}")
    
    def run(self, pdb_path: str, output_dir: str) -> List[DetectedPocket]:
        pdb_path, output_dir = Path(pdb_path), Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        work_pdb = output_dir / pdb_path.name
        shutil.copy(pdb_path, work_pdb)
        
        try:
            result = subprocess.run([str(self.fpocket_path), "-f", str(work_pdb), "-m", str(self.min_alpha_spheres)],
                                   capture_output=True, text=True, cwd=str(output_dir), timeout=300)
            if result.returncode != 0:
                raise RuntimeError(f"fpocket failed with code {result.returncode}")
        except subprocess.TimeoutExpired:
            raise RuntimeError("fpocket timed out")
        
        return self._parse_results(str(output_dir), str(pdb_path))
    
    def _parse_results(self, output_dir: str, pdb_path: str) -> List[DetectedPocket]:
        pockets = []
        output_dir, pdb_name = Path(output_dir), Path(pdb_path).stem
        fpocket_dir = output_dir / f"{pdb_name}_out"
        
        if not fpocket_dir.exists():
            return pockets
        
        info_file = fpocket_dir / f"{pdb_name}_info.txt"
        if not info_file.exists():
            for f in fpocket_dir.iterdir():
                if f.name.endswith("_info.txt"):
                    info_file = f
                    break
        
        if not info_file.exists():
            return pockets
        
        current_pocket = None
        try:
            with open(info_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line.startswith("Pocket"):
                        parts = line.split()
                        if len(parts) >= 2:
                            pocket_id = int(parts[1].replace(':', ''))
                            current_pocket = DetectedPocket(pocket_id=pocket_id, name=f"pocket_{pocket_id}",
                                                           residues=set(), center=np.zeros(3))
                            pockets.append(current_pocket)
                    elif current_pocket and "Score" in line:
                        parts = line.split(':')
                        if len(parts) >= 2:
                            try:
                                current_pocket.raw_score = float(parts[1].strip())
                            except:
                                pass
                    elif current_pocket and "Druggability" in line:
                        parts = line.split(':')
                        if len(parts) >= 2:
                            try:
                                current_pocket.probability = float(parts[1].strip())
                            except:
                                pass
        except Exception as e:
            logging.error(f"Failed to parse fpocket info: {e}")
        
        return pockets


class ConsensusScoringEngine:
    """
    DISCOVERY MODE Scoring Engine
    
    Philosophy:
    - Hub residues (network centrality) are the PRIMARY indicator of druggability
    - A pocket with hubs is valuable; without hubs, it's just a hole
    - NOVEL_CANDIDATE: Hubs present, NO validation overlap → Potential NEW drug target!
    - CONFIRMED_SITE: Hubs present, validation overlap → Known functional site
    - CRYPTIC_POCKET: Good geometry, no hubs → May open upon ligand binding
    
    Scoring Formula:
    score = geometric_base × hub_impact_factor + validation_boost + discovery_bonus
    """
    
    # Category definitions with priority (lower = higher priority in sorting)
    CATEGORIES = {
        'NOVEL_CANDIDATE': {'priority': 1, 'emoji': '🎯', 'desc': 'Potential Novel Allosteric Site'},
        'CONFIRMED_ALLOSTERIC': {'priority': 2, 'emoji': '✅', 'desc': 'Confirmed Allosteric Site'},
        'CONFIRMED_ORTHOSTERIC': {'priority': 3, 'emoji': '🔵', 'desc': 'Confirmed Orthosteric Site'},
        'CONFIRMED_DUAL': {'priority': 2, 'emoji': '⭐', 'desc': 'Overlaps Both Sites'},
        'CRYPTIC_POCKET': {'priority': 4, 'emoji': '🔮', 'desc': 'Cryptic Pocket (No Hubs)'},
        'LOW_PRIORITY': {'priority': 5, 'emoji': '⚪', 'desc': 'Low Priority Pocket'},
    }
    
    def __init__(self, config: PocketDetectionConfig):
        self.config = config
    
    def _calculate_hub_impact(self, hub_count: int, pocket_size: int) -> float:
        """
        Calculate non-linear hub impact factor.
        
        Uses logarithmic scaling with saturation to reward multiple hubs
        while avoiding over-dominance of hub-rich pockets.
        
        Formula: log(1 + hub_count * base) / log(1 + saturation * base)
        This normalizes to ~1.0 when hub_count reaches saturation point.
        """
        if hub_count == 0:
            return 0.0
        
        base = self.config.hub_impact_base
        saturation = self.config.hub_impact_saturation
        
        # Logarithmic scaling with diminishing returns
        raw_impact = math.log(1 + hub_count * base) / math.log(1 + saturation * base)
        
        # Size bonus: larger pockets with hubs are more valuable (up to a point)
        size_bonus = min(math.log2(pocket_size + 1) / 5.0, 1.2)  # Max 20% bonus
        
        # Density factor: higher hub density adds value
        density = hub_count / max(pocket_size, 1)
        density_bonus = min(density * 2, 0.3)  # Max 30% bonus for high density
        
        return min(raw_impact * size_bonus + density_bonus, 1.5)  # Cap at 1.5
    
    def _categorize_pocket(self, pocket: DetectedPocket, has_validation: bool) -> Tuple[str, int]:
        """
        Categorize pocket based on Discovery Mode logic.
        
        Priority (lower is better):
        1. NOVEL_CANDIDATE: Has hubs, NO validation overlap → THE JACKPOT!
        2. CONFIRMED_ALLOSTERIC/ORTHOSTERIC/DUAL: Has hubs, overlaps validation
        3. CRYPTIC_POCKET: Good geometry, no hubs
        4. LOW_PRIORITY: Poor geometry, no hubs
        """
        has_hubs = pocket.hub_count >= self.config.min_hubs_for_candidate
        has_allo_overlap = pocket.overlaps_allosteric
        has_orto_overlap = pocket.overlaps_orthosteric
        has_any_overlap = has_allo_overlap or has_orto_overlap
        good_geometry = pocket.geometric_score_normalized >= 0.3
        
        if has_hubs:
            if not has_validation:
                # No validation data → treat hub-containing pockets as candidates
                return 'NOVEL_CANDIDATE', self.CATEGORIES['NOVEL_CANDIDATE']['priority']
            elif not has_any_overlap:
                # Has validation data but NO overlap → NOVEL CANDIDATE!
                return 'NOVEL_CANDIDATE', self.CATEGORIES['NOVEL_CANDIDATE']['priority']
            elif has_allo_overlap and has_orto_overlap:
                return 'CONFIRMED_DUAL', self.CATEGORIES['CONFIRMED_DUAL']['priority']
            elif has_allo_overlap:
                return 'CONFIRMED_ALLOSTERIC', self.CATEGORIES['CONFIRMED_ALLOSTERIC']['priority']
            else:
                return 'CONFIRMED_ORTHOSTERIC', self.CATEGORIES['CONFIRMED_ORTHOSTERIC']['priority']
        else:
            # No hubs
            if good_geometry:
                return 'CRYPTIC_POCKET', self.CATEGORIES['CRYPTIC_POCKET']['priority']
            else:
                return 'LOW_PRIORITY', self.CATEGORIES['LOW_PRIORITY']['priority']
    
    def score_pockets(self, pockets: List[DetectedPocket], hub_residues: Set[Tuple[str, int]],
                      validation_data: Optional[Dict] = None) -> List[DetectedPocket]:
        """
        Score pockets using DISCOVERY MODE methodology.
        
        Key principles:
        1. Hub count is a MULTIPLIER, not an additive factor
        2. Pockets without hubs are penalized significantly
        3. NOVEL_CANDIDATE pockets get a discovery bonus
        4. Sorting prioritizes category first, then score
        """
        if not pockets:
            return []
        
        # Extract validation zones
        allo_zone, orto_zone = set(), set()
        has_validation = False
        if validation_data and 'zone_data' in validation_data:
            zd = validation_data['zone_data']
            allo_zone = set(tuple(r) for r in zd.get('T_Allo_5A', []))
            orto_zone = set(tuple(r) for r in zd.get('T_Orto_5A', []))
            has_validation = bool(allo_zone or orto_zone)
        
        # Normalize geometric scores
        max_score = max(max(p.raw_score for p in pockets), 0.001)
        
        for pocket in pockets:
            # =====================================================
            # STEP 1: Basic Metrics
            # =====================================================
            pocket.geometric_score_normalized = pocket.raw_score / max_score
            pocket.hubs_in_pocket = [r for r in pocket.residues if r in hub_residues]
            pocket.hub_count = len(pocket.hubs_in_pocket)
            pocket_size = len(pocket.residues)
            
            # Hub density (for reporting)
            pocket.hub_density = pocket.hub_count / max(pocket_size, 1)
            
            # =====================================================
            # STEP 2: Hub Impact Factor (Non-linear!)
            # =====================================================
            pocket.hub_impact_factor = self._calculate_hub_impact(pocket.hub_count, pocket_size)
            
            # Legacy compatibility
            pocket.hub_density_score = pocket.hub_impact_factor
            
            # =====================================================
            # STEP 3: Validation Overlap Analysis
            # =====================================================
            pocket.validation_boost = 0.0
            pocket.validation_tags = []
            
            if validation_data:
                allo_overlap = pocket.residues & allo_zone
                if allo_overlap:
                    pocket.overlaps_allosteric = True
                    pocket.allo_overlap_count = len(allo_overlap)
                    pocket.validation_boost += self.config.boost_allosteric
                
                orto_overlap = pocket.residues & orto_zone
                if orto_overlap:
                    pocket.overlaps_orthosteric = True
                    pocket.orto_overlap_count = len(orto_overlap)
                    pocket.validation_boost += self.config.boost_orthosteric
            
            # =====================================================
            # STEP 4: Category Assignment (Discovery Mode!)
            # =====================================================
            category, priority = self._categorize_pocket(pocket, has_validation)
            pocket.discovery_category = category
            pocket.category_priority = priority
            pocket.validation_tags.append(category)
            
            # Add detail tags
            if pocket.overlaps_allosteric:
                pocket.validation_tags.append("ALLO_OVERLAP")
            if pocket.overlaps_orthosteric:
                pocket.validation_tags.append("ORTO_OVERLAP")
            
            # =====================================================
            # STEP 5: Discovery Bonus Calculation
            # =====================================================
            pocket.novelty_bonus = 0.0
            if category == 'NOVEL_CANDIDATE':
                # THE JACKPOT: Novel candidate with hubs!
                pocket.novelty_bonus = self.config.novelty_bonus
            elif category in ('CONFIRMED_ALLOSTERIC', 'CONFIRMED_ORTHOSTERIC', 'CONFIRMED_DUAL'):
                # Confirmed site bonus
                pocket.novelty_bonus = self.config.confirmation_bonus
            
            # =====================================================
            # STEP 6: Final Consensus Score
            # =====================================================
            # Base geometric contribution
            geo_component = self.config.weight_geometric * pocket.geometric_score_normalized
            
            # Hub impact as a MULTIPLIER on base score
            if pocket.hub_count > 0:
                hub_component = self.config.weight_hub_impact * pocket.hub_impact_factor
            else:
                # NO HUBS = Penalty! Reduce score significantly
                hub_component = 0.0
                geo_component *= self.config.no_hub_penalty
            
            # Validation contribution
            val_component = self.config.weight_validation * min(pocket.validation_boost, 1.0)
            
            # Discovery bonus (additive)
            discovery_component = pocket.novelty_bonus
            
            # Final score
            pocket.consensus_score = geo_component + hub_component + val_component + discovery_component
        
        # =====================================================
        # STEP 7: Sort by Category Priority, then by Score
        # =====================================================
        # This ensures NOVEL_CANDIDATE pockets appear first even if
        # a CONFIRMED_SITE has a slightly higher raw score
        pockets.sort(key=lambda p: (p.category_priority, -p.consensus_score))
        
        return pockets[:self.config.max_pockets]
    
    def generate_report(self, pockets: List[DetectedPocket]) -> pd.DataFrame:
        """Generate detailed report with Discovery Mode categories."""
        data = []
        for p in pockets:
            category_info = self.CATEGORIES.get(p.discovery_category, {})
            emoji = category_info.get('emoji', '❓')
            
            data.append({
                'Rank': len(data) + 1,
                'Category': f"{emoji} {p.discovery_category}",
                'Pocket_ID': p.pocket_id,
                'Pocket_Name': p.name,
                'Size': len(p.residues),
                'Hub_Count': p.hub_count,
                'Hub_Impact': round(p.hub_impact_factor, 3),
                'Geometric': round(p.geometric_score_normalized, 3),
                'Novelty_Bonus': round(p.novelty_bonus, 3),
                'Consensus_Score': round(p.consensus_score, 3),
                'Allo_Overlap': p.allo_overlap_count,
                'Orto_Overlap': p.orto_overlap_count,
                'Raw_Score': round(p.raw_score, 2),
                'Tags': ', '.join(p.validation_tags) if p.validation_tags else '-'
            })
        return pd.DataFrame(data)


class PocketVisualizationGenerator:
    """
    SCIENTIFIC DARK MODE PyMOL scripts for Pocket Detection with:
    - Dark glass protein representation (gray20/gray30, semi-transparent)
    - Pockets as NEON surfaces + bright mesh overlay (cyan, magenta, lime, etc.)
    - Hub residues as Ball & Stick with SMALL CA spheres (not gumballs!)
    - Pitch black background with strong Ambient Occlusion & Depth Cueing
    - High specularity for "wet/glowing" neon effect
    - Gray outlines (visible on black background)
    """
    
    # (primary_color, mesh_color, highlight_color) for each pocket - NEON PALETTE for Dark Mode
    POCKET_COLORS = [
        ('cyan', 'palecyan', 'aquamarine'),           # Neon Cyan
        ('magenta', 'lightmagenta', 'hotpink'),       # Neon Magenta
        ('chartreuse', 'greenyellow', 'limon'),       # Neon Lime/Chartreuse
        ('brightorange', 'lightorange', 'tv_orange'), # Neon Orange
        ('hotpink', 'lightpink', 'warmpink'),         # Hot Pink
        ('tv_blue', 'lightblue', 'slate'),            # Electric Blue
        ('yellowgreen', 'paleyellow', 'tv_yellow'),   # Neon Yellow-Green
        ('deeppurple', 'violet', 'purple'),           # Electric Purple
        ('limegreen', 'palegreen', 'lime'),           # Bright Lime
        ('salmon', 'lightsalmon', 'deepsalmon'),      # Neon Coral
    ]
    
    def __init__(self, main_structure_path: str):
        self.main_structure_path = str(Path(main_structure_path)).replace('\\', '/')
    
    def generate_script(self, pockets: List[DetectedPocket], hub_residues: Set[Tuple[str, int]],
                        validation_data: Optional[Dict] = None, allo_file: Optional[str] = None,
                        orto_file: Optional[str] = None) -> str:
        script_parts = [
            self._header(),
            self._global_settings(),  # NEW: Apply global aesthetic settings FIRST
            self._load_structure(),
            self._create_ghost_protein()
        ]
        
        # Create pocket objects with surface + mesh overlay
        for i, pocket in enumerate(pockets[:10]):
            color_idx = min(i, len(self.POCKET_COLORS) - 1)
            script_parts.append(self._create_pocket_object(pocket, i + 1, self.POCKET_COLORS[color_idx]))
        
        # Hub residues as Ball & Stick (NOT gumballs!)
        script_parts.append(self._create_hub_objects(pockets, hub_residues))
        
        if validation_data:
            script_parts.append(self._create_validation_zones(validation_data))
        
        script_parts.extend([
            self._publication_settings(),
            self._visibility_controls(len(pockets[:10])),
            self._footer()
        ])
        return '\n'.join(script_parts)
    
    def _header(self) -> str:
        return f"""# ============================================================================
# RIN Analyzer v7.0.0 - SCIENTIFIC DARK MODE VISUALIZATION
# Generated: {pd.Timestamp.now().strftime('%Y-%m-%d %H:%M:%S')}
# ============================================================================
# VISUALIZATION STYLE: "The Void" - High-Contrast Neon on Black
#   - Background: Pitch black with depth fog fading to darkness
#   - Protein: Dark glass ghost (gray20/gray30, semi-transparent) + Dark cartoon
#   - Pockets: NEON surfaces (cyan, magenta, lime, orange, pink, electric blue)
#       * Surface: Neon color, 40% transparent (glowing effect)
#       * Mesh: Brighter wireframe overlay for sharp boundary definition
#   - Hub Residues: Ball & Stick (small CA spheres only!)
#       * Hubs in Pockets: Bright sticks + small yellow CA spheres
#       * Orphan Hubs: Subtle thin sticks (no spheres)
# RENDERING: Ray Trace Mode 1 + Strong AO + High Specularity (wet/glowing look)
# ============================================================================
"""

    def _global_settings(self) -> str:
        """Apply global aesthetic settings BEFORE loading structure - SCIENTIFIC DARK MODE"""
        return """
# =============================================================================
# GLOBAL AESTHETIC SETTINGS - SCIENTIFIC DARK MODE ("The Void")
# =============================================================================
# Anti-aliasing for smooth edges
set antialias, 2
set hash_max, 300

# Orthographic projection (no perspective distortion - better for figures)
set orthoscopic, on

# Background: PITCH BLACK (The Void)
bg_color black

# Ray Trace Mode 1: Normal colors with GRAY outlines (visible on black bg!)
set ray_trace_mode, 1
set ray_trace_gain, 0.6
set ray_trace_color, gray40

# Depth Cueing (fog fading into darkness)
set depth_cue, 1
set fog_start, 0.35
set fog, 0.9

# Ambient Occlusion (deep shadows in crevices for 3D depth)
set ambient_occlusion_mode, 1
set ambient_occlusion_scale, 30
set ambient_occlusion_smooth, 12

# Two-sided lighting (ensures visibility from all angles)
set two_sided_lighting, on

# HIGH SPECULARITY - Wet/Glowing Neon Effect
set specular, 0.8
set specular_intensity, 0.6
set spec_reflect, 0.8
set shininess, 80
set spec_power, 200

# Soft shadows
set ray_shadows, on
set ray_shadow_decay_factor, 0.15

# Enhanced lighting for dark background
set ambient, 0.25
set direct, 0.7
set reflect, 0.5
set light_count, 4
"""
    
    def _load_structure(self) -> str:
        return f"""
load {self.main_structure_path}, main_protein
remove solvent
remove resn HOH+WAT
"""
    
    def _create_ghost_protein(self) -> str:
        return """
# =============================================================================
# COMPOSITE PROTEIN REPRESENTATION - DARK GHOST (Dark Glass Casing)
# =============================================================================
# Layer 1: Cartoon - Dark charcoal secondary structure
hide everything, main_protein
show cartoon, main_protein
color gray30, main_protein
set cartoon_transparency, 0.50, main_protein
set cartoon_fancy_helices, 1
set cartoon_smooth_loops, 1
set cartoon_loop_radius, 0.3

# Layer 2: Dark Glass Surface - Semi-transparent dark casing around neon pockets
create protein_ghost, main_protein
hide everything, protein_ghost
show surface, protein_ghost
color gray20, protein_ghost
set transparency, 0.75, protein_ghost
set surface_quality, 1
set surface_type, 0

# Glass-like material for protein ghost (subtle sheen, not overpowering neon)
set spec_reflect, 0.4, protein_ghost
set spec_power, 80, protein_ghost
"""
    
    def _create_pocket_object(self, pocket: DetectedPocket, rank: int, colors: Tuple[str, str, str]) -> str:
        """Create pocket with Surface + Mesh overlay for clear boundary definition"""
        if not pocket.residues:
            return f"# Pocket {rank}: No residues"
        
        chain_residues = defaultdict(list)
        for chain, resid in pocket.residues:
            chain_residues[chain].append(resid)
        
        parts = [f"(chain {chain} and resi {'+'.join(map(str, sorted(resids)))})" for chain, resids in chain_residues.items()]
        selection = " or ".join(parts)
        tags_str = ', '.join(pocket.validation_tags) if pocket.validation_tags else 'None'
        
        primary_color, mesh_color, highlight_color = colors
        
        return f"""
# =============================================================================
# POCKET {rank} - Score: {pocket.consensus_score:.3f} | Hubs: {pocket.hub_count} | Tags: {tags_str}
# =============================================================================
# Layer 1: NEON Surface (semi-transparent, glowing effect in the dark)
create pocket_{rank}_surf, main_protein and ({selection})
hide everything, pocket_{rank}_surf
show surface, pocket_{rank}_surf
color {primary_color}, pocket_{rank}_surf
set transparency, 0.40, pocket_{rank}_surf
set surface_quality, 2

# Enhance neon glow on pocket surfaces
set spec_reflect, 0.9, pocket_{rank}_surf
set spec_power, 150, pocket_{rank}_surf

# Layer 2: Bright Mesh Overlay (sharp wireframe boundary in the dark)
create pocket_{rank}_mesh, main_protein and ({selection})
hide everything, pocket_{rank}_mesh
show mesh, pocket_{rank}_mesh
color {mesh_color}, pocket_{rank}_mesh
set mesh_width, 0.8

# Group pocket objects
group pocket_{rank}_grp, pocket_{rank}_surf pocket_{rank}_mesh
"""
    
    def _create_hub_objects(self, pockets: List[DetectedPocket], all_hubs: Set[Tuple[str, int]]) -> str:
        """
        Create hub residues as BALL & STICK representation (NOT gumballs!)
        - Shows side chain chemistry (important for allosteric sites)
        - CA atom as SMALL sphere (scale 0.3) marks the hub position
        - Sticks show where the residue is pointing
        - BRIGHT colors to pop against dark protein in Dark Mode
        """
        script = """
# =============================================================================
# HUB RESIDUE VISUALIZATION (Ball & Stick Style - Neon Highlights)
# =============================================================================
"""
        if not all_hubs:
            return script + "# No hub residues\n"
        
        hubs_in_pockets = set()
        for pocket in pockets:
            hubs_in_pockets.update(pocket.hubs_in_pocket)
        orphan_hubs = all_hubs - hubs_in_pockets
        
        # Build selection strings
        def build_sel(residues):
            if not residues:
                return None
            chain_res = defaultdict(list)
            for chain, resid in residues:
                chain_res[chain].append(resid)
            return " or ".join(f"(chain {ch} and resi {'+'.join(map(str, sorted(res)))})" for ch, res in chain_res.items())
        
        all_hub_sel = build_sel(all_hubs)
        
        # Base layer: All hubs as thin sticks (subtle gray - visible on dark bg)
        script += f"""
# Base Layer: All hubs (subtle reference - gray on dark background)
create all_hubs, main_protein and ({all_hub_sel})
hide everything, all_hubs
show sticks, all_hubs
set stick_radius, 0.15, all_hubs
color gray50, all_hubs
util.cbag all_hubs  # Color by atom type (N=blue, O=red, S=yellow)
"""
        
        # Hubs in pockets: Prominent Ball & Stick with BRIGHT NEON colors
        if hubs_in_pockets:
            sel_in = build_sel(hubs_in_pockets)
            script += f"""
# Hubs Inside Pockets: GLOWING Ball & Stick (bright white carbons for contrast)
create hubs_in_pocket, main_protein and ({sel_in})
hide everything, hubs_in_pocket

# Thick sticks for side chains - WHITE carbons to glow against dark protein
show sticks, hubs_in_pocket
set stick_radius, 0.22, hubs_in_pocket
color white, hubs_in_pocket and elem C
util.cnc hubs_in_pocket  # Color N=blue, O=red, S=yellow by element

# SMALL spheres ONLY on CA atoms (scale 0.3 - not gumballs!)
show spheres, hubs_in_pocket and name CA
set sphere_scale, 0.30, hubs_in_pocket
color tv_yellow, hubs_in_pocket and name CA

# Ensure hubs are visible above pocket surfaces
set stick_transparency, 0, hubs_in_pocket

# Add glow effect to hub sticks
set spec_reflect, 0.7, hubs_in_pocket
"""
        
        # Orphan hubs: Very subtle (thin gray sticks, no spheres) - visible on dark bg
        if orphan_hubs:
            sel_out = build_sel(orphan_hubs)
            script += f"""
# Orphan Hubs: Subtle thin sticks (potential novel sites - gray60 visible on black)
create orphan_hubs, main_protein and ({sel_out})
hide everything, orphan_hubs
show sticks, orphan_hubs
set stick_radius, 0.10, orphan_hubs
color gray60, orphan_hubs
set stick_transparency, 0.2, orphan_hubs
# No CA spheres - keep orphans subtle
"""
        
        # Group all hub objects
        script += """
# Group hub objects for easy toggle
group hub_residues_grp, all_hubs hubs_in_pocket orphan_hubs
"""
        return script
    
    def _create_validation_zones(self, validation_data: Dict) -> str:
        script = "\n# VALIDATION ZONES (NEON COLORS FOR DARK MODE)\n"
        if 'zone_data' not in validation_data:
            return script
        
        zd = validation_data['zone_data']
        
        def build_sel(residues):
            if not residues:
                return "none"
            chain_res = defaultdict(list)
            for r in residues:
                if isinstance(r, (list, tuple)) and len(r) >= 2:
                    chain_res[r[0]].append(r[1])
            parts = [f"(chain {ch} and resi {'+'.join(map(str, sorted(res)))})" for ch, res in chain_res.items()]
            return " or ".join(parts) if parts else "none"
        
        # Neon colors for dark mode: Magenta for Allo, Cyan for Orto
        for zone_name, color, rep in [('T_Allo_Core', 'magenta', 'surface'), ('T_Allo_Shell', 'hotpink', 'mesh'),
                                       ('T_Orto_Core', 'cyan', 'surface'), ('T_Orto_Shell', 'aquamarine', 'mesh')]:
            sel = build_sel(zd.get(zone_name, []))
            if sel != "none":
                obj_name = zone_name.lower().replace('_', '_')
                script += f"""
create {obj_name}, main_protein and ({sel})
hide everything, {obj_name}
show {rep}, {obj_name}
color {color}, {obj_name}
"""
                if rep == 'surface':
                    script += f"set transparency, 0.4, {obj_name}\n"
                    script += f"set spec_reflect, 0.9, {obj_name}\n"
                else:
                    script += f"set mesh_width, 0.8, {obj_name}\n"
        
        return script
    
    def _publication_settings(self) -> str:
        return """
# =============================================================================
# FINAL SCENE SETUP - DARK MODE OPTIMIZED
# =============================================================================
# Camera and view
zoom all, buffer=5
orient

# Fine-tune lighting for dark background (enhance neon glow)
set ambient, 0.20
set direct, 0.75
set reflect, 0.6

# Surface quality for final render
set surface_quality, 2
set cartoon_sampling, 14

# Ensure black background renders correctly
set ray_opaque_background, off
"""
    
    def _visibility_controls(self, num_pockets: int) -> str:
        script = """
# =============================================================================
# VISIBILITY DEFAULTS (Toggle as needed)
# =============================================================================
# Protein context
enable main_protein
enable protein_ghost

"""
        # Enable top 3 pockets by default
        for i in range(1, min(4, num_pockets + 1)):
            script += f"enable pocket_{i}_grp\n"
        for i in range(4, num_pockets + 1):
            script += f"disable pocket_{i}_grp\n"
        
        script += """
# Hub residues
enable hub_residues_grp
enable hubs_in_pocket
disable orphan_hubs
disable all_hubs  # Disable base layer (hubs_in_pocket is more visible)
"""
        return script
    
    def _footer(self) -> str:
        return """
# =============================================================================
# RENDERING COMMANDS (Uncomment to use) - DARK MODE
# =============================================================================
# Standard publication quality:
#   ray 2400, 1800
#   png output_pocket_viz_dark.png, dpi=300
#
# High resolution for poster/print:
#   ray 4800, 3600
#   png output_highres_dark.png, dpi=600
#
# Quick preview:
#   ray 1200, 900
#
# TIP: Dark mode renders look best with transparent background for overlays:
#   set ray_opaque_background, off
#   png output_transparent.png, dpi=300
# =============================================================================
print "RIN Analyzer v7.0.0 - Scientific Dark Mode Visualization Loaded"
print "TIP: Neon pockets glow against the dark protein - use 'ray' for best results"
"""


class ValidationPyMOLGenerator:
    """
    SCIENTIFIC DARK MODE PyMOL scripts for Validation with:
    - Dark glass protein representation (dark charcoal cartoon + surface)
    - Core zones as NEON solid surfaces with bright mesh overlay
    - Shell zones (5Å) as neon mesh only (visually distinct from core)
    - Hub overlaps as Ball & Stick with SMALL CA spheres (NOT gumballs!)
    - Strong Ambient Occlusion, Depth Cueing, High Specularity
    """
    
    def __init__(self, main_structure_path: str):
        self.main_structure_path = str(Path(main_structure_path)).replace('\\', '/')
    
    def generate_script(self, validation_results: Dict, allo_file: str, orto_file: Optional[str] = None) -> str:
        script_parts = [
            self._header(),
            self._global_settings(),  # Apply dark mode aesthetics FIRST
            self._load_structure(),
            self._create_ghost_protein()
        ]
        
        zone_data = validation_results.get('zone_data', {})
        predicted_hubs = set(tuple(r) for r in zone_data.get('predicted_hubs', []))
        
        script_parts.extend([
            self._create_allosteric_zones(zone_data),
            self._create_orthosteric_zones(zone_data),
            self._create_hub_overlaps(zone_data, predicted_hubs),
            self._publication_settings(),
            self._visibility_controls(),
            self._footer()
        ])
        return '\n'.join(script_parts)
    
    def _header(self) -> str:
        return f"""# ============================================================================
# RIN Analyzer v7.0.0 - SCIENTIFIC DARK MODE VALIDATION VISUALIZATION
# Generated: {pd.Timestamp.now().strftime('%Y-%m-%d %H:%M:%S')}
# ============================================================================
# VISUALIZATION STYLE: "The Void" - High-Contrast Neon on Black
#   - Background: Pitch black with depth fog fading to darkness
#   - Protein: Dark glass ghost (gray20/gray30, semi-transparent casing)
#   - Allosteric Zone: Core = NEON MAGENTA surface + bright mesh, Shell = Pink mesh
#   - Orthosteric Zone: Core = NEON CYAN surface + bright mesh, Shell = Aqua mesh
#   - Hub Residues: Ball & Stick with SMALL CA spheres (scale 0.3!)
#       * Core Hubs: Bright white sticks + yellow CA sphere (True Positives)
#       * Shell Hubs: Orange sticks + small CA sphere (Proximal Positives)  
#       * Orphan Hubs: Subtle gray sticks (Potential Novel Sites)
# RENDERING: Ray Trace Mode 1 + Strong AO + High Specularity (wet/glowing)
# ============================================================================
"""

    def _global_settings(self) -> str:
        """Apply global aesthetic settings BEFORE loading structure - SCIENTIFIC DARK MODE"""
        return """
# =============================================================================
# GLOBAL AESTHETIC SETTINGS - SCIENTIFIC DARK MODE ("The Void")
# =============================================================================
set antialias, 2
set hash_max, 300
set orthoscopic, on

# Background: PITCH BLACK (The Void)
bg_color black

# Ray Trace Mode 1: Normal colors with GRAY outlines (visible on black bg!)
set ray_trace_mode, 1
set ray_trace_gain, 0.6
set ray_trace_color, gray40

# Depth Cueing (fog fading into darkness)
set depth_cue, 1
set fog_start, 0.35
set fog, 0.9

# Ambient Occlusion (deep shadows in crevices for 3D depth)
set ambient_occlusion_mode, 1
set ambient_occlusion_scale, 30
set ambient_occlusion_smooth, 12

# Two-sided lighting (ensures visibility from all angles)
set two_sided_lighting, on

# HIGH SPECULARITY - Wet/Glowing Neon Effect
set specular, 0.8
set specular_intensity, 0.6
set spec_reflect, 0.8
set shininess, 80
set spec_power, 200

# Soft shadows
set ray_shadows, on
set ray_shadow_decay_factor, 0.15

# Enhanced lighting for dark background
set ambient, 0.25
set direct, 0.7
set reflect, 0.5
set light_count, 4
"""
    
    def _load_structure(self) -> str:
        return f"""
load {self.main_structure_path}, main_protein
remove solvent
remove resn HOH+WAT
"""
    
    def _create_ghost_protein(self) -> str:
        return """
# =============================================================================
# COMPOSITE PROTEIN REPRESENTATION - DARK GHOST (Dark Glass Casing)
# =============================================================================
# Layer 1: Cartoon - Dark charcoal secondary structure
hide everything, main_protein
show cartoon, main_protein
color gray30, main_protein
set cartoon_transparency, 0.50, main_protein
set cartoon_fancy_helices, 1
set cartoon_smooth_loops, 1
set cartoon_loop_radius, 0.3

# Layer 2: Dark Glass Surface - Semi-transparent dark casing around neon zones
create protein_ghost, main_protein
hide everything, protein_ghost
show surface, protein_ghost
color gray20, protein_ghost
set transparency, 0.75, protein_ghost
set surface_quality, 1

# Glass-like material for protein ghost (subtle sheen, not overpowering neon)
set spec_reflect, 0.4, protein_ghost
set spec_power, 80, protein_ghost
"""
    
    def _build_selection(self, residues: List) -> str:
        if not residues:
            return "none"
        chain_res = defaultdict(list)
        for r in residues:
            if isinstance(r, (list, tuple)) and len(r) >= 2:
                chain_res[r[0]].append(r[1])
        parts = [f"(chain {ch} and resi {'+'.join(map(str, sorted(res)))})" for ch, res in chain_res.items()]
        return " or ".join(parts) if parts else "none"
    
    def _create_allosteric_zones(self, zone_data: Dict) -> str:
        script = """
# =============================================================================
# ALLOSTERIC ZONES (NEON MAGENTA/HOTPINK color scheme)
# =============================================================================
"""
        allo_core_sel = self._build_selection(zone_data.get('T_Allo_Core', []))
        if allo_core_sel != "none":
            script += f"""
# Allosteric Core: NEON MAGENTA surface + bright mesh overlay
create Allo_Core_surf, main_protein and ({allo_core_sel})
hide everything, Allo_Core_surf
show surface, Allo_Core_surf
color magenta, Allo_Core_surf
set transparency, 0.40, Allo_Core_surf
set surface_quality, 2

# Enhance neon glow
set spec_reflect, 0.9, Allo_Core_surf
set spec_power, 150, Allo_Core_surf

create Allo_Core_mesh, main_protein and ({allo_core_sel})
hide everything, Allo_Core_mesh
show mesh, Allo_Core_mesh
color lightmagenta, Allo_Core_mesh
set mesh_width, 0.8

group Allo_Core_grp, Allo_Core_surf Allo_Core_mesh
"""
        
        allo_shell_sel = self._build_selection(zone_data.get('T_Allo_Shell', []))
        if allo_shell_sel != "none":
            script += f"""
# Allosteric Shell (5A): NEON PINK Mesh ONLY (distinct from core)
create Allo_Shell, main_protein and ({allo_shell_sel})
hide everything, Allo_Shell
show mesh, Allo_Shell
color hotpink, Allo_Shell
set mesh_width, 0.9
"""
        return script
    
    def _create_orthosteric_zones(self, zone_data: Dict) -> str:
        script = """
# =============================================================================
# ORTHOSTERIC ZONES (NEON CYAN/AQUAMARINE color scheme)
# =============================================================================
"""
        orto_core_sel = self._build_selection(zone_data.get('T_Orto_Core', []))
        if orto_core_sel != "none":
            script += f"""
# Orthosteric Core: NEON CYAN surface + bright mesh overlay
create Orto_Core_surf, main_protein and ({orto_core_sel})
hide everything, Orto_Core_surf
show surface, Orto_Core_surf
color cyan, Orto_Core_surf
set transparency, 0.40, Orto_Core_surf
set surface_quality, 2

# Enhance neon glow
set spec_reflect, 0.9, Orto_Core_surf
set spec_power, 150, Orto_Core_surf

create Orto_Core_mesh, main_protein and ({orto_core_sel})
hide everything, Orto_Core_mesh
show mesh, Orto_Core_mesh
color palecyan, Orto_Core_mesh
set mesh_width, 0.8

group Orto_Core_grp, Orto_Core_surf Orto_Core_mesh
"""
        
        orto_shell_sel = self._build_selection(zone_data.get('T_Orto_Shell', []))
        if orto_shell_sel != "none":
            script += f"""
# Orthosteric Shell (5A): NEON AQUAMARINE Mesh ONLY (distinct from core)
create Orto_Shell, main_protein and ({orto_shell_sel})
hide everything, Orto_Shell
show mesh, Orto_Shell
color aquamarine, Orto_Shell
set mesh_width, 0.9
"""
        return script
    
    def _create_hub_overlaps(self, zone_data: Dict, predicted_hubs: Set[Tuple[str, int]]) -> str:
        """
        Create hub residues as BALL & STICK representation (NOT gumballs!)
        Color-coded by overlap with validation zones - BRIGHT for dark mode:
        - Core: White carbons + Yellow CA (True Positives - HIGH CONTRAST)
        - Shell: Bright Orange carbons + Orange CA (Proximal Positives)
        - Orphan: Gray (Potential Novel Sites - visible on dark bg)
        """
        script = """
# =============================================================================
# HUB RESIDUE VISUALIZATION (Ball & Stick Style - Neon Highlights)
# =============================================================================
"""
        if not predicted_hubs:
            return script + "# No predicted hubs\n"
        
        allo_core = set(tuple(r) for r in zone_data.get('T_Allo_Core', []))
        allo_shell = set(tuple(r) for r in zone_data.get('T_Allo_Shell', []))
        orto_core = set(tuple(r) for r in zone_data.get('T_Orto_Core', []))
        orto_shell = set(tuple(r) for r in zone_data.get('T_Orto_Shell', []))
        
        hubs_in_core = predicted_hubs & (allo_core | orto_core)
        shell_only = (allo_shell | orto_shell) - (allo_core | orto_core)
        hubs_in_shell = predicted_hubs & shell_only
        orphan_hubs = predicted_hubs - (allo_core | allo_shell | orto_core | orto_shell)
        
        # Base layer: All hubs as thin sticks (subtle gray - visible on dark bg)
        all_hub_sel = self._build_selection(list(predicted_hubs))
        script += f"""
# Base Layer: All hubs (subtle reference - gray50 visible on black bg)
create All_Hubs, main_protein and ({all_hub_sel})
hide everything, All_Hubs
show sticks, All_Hubs
set stick_radius, 0.12, All_Hubs
color gray50, All_Hubs
util.cbag All_Hubs
"""
        
        # Hubs in Core: PROMINENT Ball & Stick (WHITE carbons = TRUE POSITIVE - HIGH CONTRAST)
        if hubs_in_core:
            core_sel = self._build_selection(list(hubs_in_core))
            script += f"""
# Hubs in Core: TRUE POSITIVES (BRIGHT WHITE carbons for maximum contrast)
create Hubs_In_Core, main_protein and ({core_sel})
hide everything, Hubs_In_Core

# Thick sticks for side chains - WHITE carbons glow against dark protein
show sticks, Hubs_In_Core
set stick_radius, 0.22, Hubs_In_Core
color white, Hubs_In_Core and elem C
util.cnc Hubs_In_Core  # Color N=blue, O=red, S=yellow by element

# SMALL CA spheres (scale 0.30 - NOT gumballs!)
show spheres, Hubs_In_Core and name CA
set sphere_scale, 0.30, Hubs_In_Core
color tv_yellow, Hubs_In_Core and name CA

# Add glow effect
set spec_reflect, 0.7, Hubs_In_Core
"""
        
        # Hubs in Shell: Medium sticks (Bright Orange = PROXIMAL POSITIVE)
        if hubs_in_shell:
            shell_sel = self._build_selection(list(hubs_in_shell))
            script += f"""
# Hubs in Shell: PROXIMAL POSITIVES (bright orange - visible on dark bg)
create Hubs_In_Shell, main_protein and ({shell_sel})
hide everything, Hubs_In_Shell

# Medium sticks - bright orange carbons
show sticks, Hubs_In_Shell
set stick_radius, 0.18, Hubs_In_Shell
color brightorange, Hubs_In_Shell and elem C
util.cnc Hubs_In_Shell

# SMALL CA spheres (scale 0.25)
show spheres, Hubs_In_Shell and name CA
set sphere_scale, 0.25, Hubs_In_Shell
color tv_orange, Hubs_In_Shell and name CA
"""
        
        # Orphan hubs: Very thin sticks (Gray = POTENTIAL NOVEL SITES - visible on dark bg)
        if orphan_hubs:
            orphan_sel = self._build_selection(list(orphan_hubs))
            script += f"""
# Orphan Hubs: POTENTIAL NOVEL SITES (gray60 - visible on black bg)
create Orphan_Hubs, main_protein and ({orphan_sel})
hide everything, Orphan_Hubs

# Very thin sticks - gray60 visible against dark protein
show sticks, Orphan_Hubs
set stick_radius, 0.10, Orphan_Hubs
color gray60, Orphan_Hubs
set stick_transparency, 0.2, Orphan_Hubs
# No CA spheres - keep orphans subtle
"""
        
        # Group all hub objects
        script += """
# Group hub objects for easy toggle
group Hub_Overlaps_grp, All_Hubs Hubs_In_Core Hubs_In_Shell Orphan_Hubs
"""
        return script
    
    def _publication_settings(self) -> str:
        return """
# =============================================================================
# FINAL SCENE SETUP - DARK MODE OPTIMIZED
# =============================================================================
# Camera and view
zoom all, buffer=5
orient

# Fine-tune lighting for dark background (enhance neon glow)
set ambient, 0.20
set direct, 0.75
set reflect, 0.6

# Surface quality
set surface_quality, 2
set cartoon_sampling, 14

# Ensure black background renders correctly
set ray_opaque_background, off
"""
    
    def _visibility_controls(self) -> str:
        return """
# =============================================================================
# VISIBILITY DEFAULTS (Toggle as needed)
# =============================================================================
# Protein context
enable main_protein
enable protein_ghost

# Allosteric zones
enable Allo_Core_grp
enable Allo_Shell

# Orthosteric zones  
enable Orto_Core_grp
enable Orto_Shell

# Hub overlaps
enable Hub_Overlaps_grp
enable Hubs_In_Core
enable Hubs_In_Shell
disable Orphan_Hubs
disable All_Hubs  # Disable base layer
"""
    
    def _footer(self) -> str:
        return """
# =============================================================================
# RENDERING COMMANDS (Uncomment to use) - DARK MODE
# =============================================================================
# Standard publication quality:
#   ray 2400, 1800
#   png validation_viz_dark.png, dpi=300
#
# High resolution for poster/print:
#   ray 4800, 3600
#   png validation_highres_dark.png, dpi=600
#
# Quick preview:
#   ray 1200, 900
#
# TIP: Dark mode renders look best with transparent background for overlays:
#   set ray_opaque_background, off
#   png validation_transparent.png, dpi=300
# =============================================================================
print "RIN Analyzer v7.0.0 - Scientific Dark Mode Validation Loaded"
print "TIP: Neon zones glow against the dark protein - use 'ray' for best results"
"""


class PocketDetectionThread(QThread):
    """Background thread for pocket detection and scoring"""
    
    progress_update = Signal(int, str)
    detection_complete = Signal(dict)
    error_occurred = Signal(str)
    
    def __init__(self, config: PocketDetectionConfig, main_structure_path: str,
                 hub_residues: Set[Tuple[str, int]], validation_data: Optional[Dict] = None,
                 output_dir: Optional[str] = None):
        super().__init__()
        self.config = config
        self.main_structure_path = main_structure_path
        self.hub_residues = hub_residues
        self.validation_data = validation_data
        self.output_dir = output_dir or tempfile.mkdtemp(prefix="rin_pockets_")
        self.is_running = True
    
    def run(self):
        try:
            self.progress_update.emit(10, f"Running {self.config.tool.value}...")
            
            runner = P2RankRunner(self.config.tool_path, self.config.p2rank_model) if self.config.tool == PocketTool.P2RANK else FpocketRunner(self.config.tool_path, self.config.fpocket_min_alpha_spheres)
            pockets = runner.run(self.main_structure_path, self.output_dir)
            
            self.progress_update.emit(50, f"Found {len(pockets)} pockets. Scoring...")
            
            scoring_engine = ConsensusScoringEngine(self.config)
            scored_pockets = scoring_engine.score_pockets(pockets, self.hub_residues, self.validation_data)
            report_df = scoring_engine.generate_report(scored_pockets)
            
            self.progress_update.emit(90, "Generating visualization...")
            
            viz_generator = PocketVisualizationGenerator(self.main_structure_path)
            allo_file = self.validation_data.get('metadata', {}).get('allo_file') if self.validation_data else None
            orto_file = self.validation_data.get('metadata', {}).get('orto_file') if self.validation_data else None
            pymol_script = viz_generator.generate_script(scored_pockets, self.hub_residues, self.validation_data, allo_file, orto_file)
            
            self.progress_update.emit(100, "Complete!")
            self.detection_complete.emit({
                'pockets': scored_pockets, 'report': report_df, 'pymol_script': pymol_script,
                'output_dir': self.output_dir, 'tool_used': self.config.tool.value
            })
        except Exception as e:
            self.error_occurred.emit(f"Pocket detection error: {str(e)}\n{traceback.format_exc()}")
    
    def stop(self):
        self.is_running = False


class RINAnalyzerGUI(QMainWindow):
    """Main application window - Ligand-Free Edition with Publication-Quality Visualization"""
    
    def __init__(self):
        super().__init__()
        self.platform_helper = PlatformHelper()
        self.current_results = {}
        self.analysis_thread = None
        self.validation_thread = None
        self.pocket_thread = None
        self.validation_results = None
        self.pocket_results = None
        self.pocket_config = PocketDetectionConfig()
        self.output_dir = str(self.platform_helper.get_documents_directory() / "RIN_Analyzer_Results")
        self.init_ui()
        self.setup_style()
    
    def init_ui(self):
        self.setWindowTitle(f"{APP_NAME} v{APP_VERSION}")
        self.setGeometry(100, 100, 1700, 1100)
        
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)
        main_layout.setSpacing(0)
        main_layout.setContentsMargins(8, 8, 8, 8)
        
        self.main_tabs = QTabWidget()
        self.main_tabs.addTab(self.create_rin_analysis_tab(), "  📊  RIN Analysis  ")
        self.main_tabs.addTab(self.create_validation_tab(), "  ✓  Validation  ")
        self.main_tabs.addTab(self.create_pocket_detection_tab(), "  🔬  Pocket Detection  ")
        main_layout.addWidget(self.main_tabs)
        
        self.create_menu_bar()
        self.create_status_bar()
    
    def create_rin_analysis_tab(self) -> QWidget:
        tab = QWidget()
        layout = QHBoxLayout(tab)
        layout.setSpacing(0)
        layout.setContentsMargins(12, 12, 12, 12)
        
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.addWidget(self.create_left_panel())
        splitter.addWidget(self.create_right_panel())
        splitter.setSizes([420, 1280])
        splitter.setHandleWidth(4)
        layout.addWidget(splitter)
        return tab
    
    def create_left_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)
        layout.setSpacing(12)
        layout.setContentsMargins(0, 0, 12, 0)
        
        # Title with icon-like styling
        title_label = QLabel("⚛️  RIN Analyzer")
        title_label.setObjectName("titleLabel")
        title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title_label)
        
        # Analysis Parameters Group
        params_group = QGroupBox("Analysis Parameters")
        params_layout = QFormLayout()
        params_layout.setSpacing(12)
        params_layout.setContentsMargins(16, 24, 16, 16)
        
        self.cutoff_input = QDoubleSpinBox()
        self.cutoff_input.setRange(1.0, 10.0)
        self.cutoff_input.setValue(DEFAULT_CUTOFF)
        self.cutoff_input.setSingleStep(0.1)
        self.cutoff_input.setDecimals(1)
        self.cutoff_input.setSuffix(" Å")
        self.cutoff_input.setMinimumHeight(32)
        params_layout.addRow("Contact Cutoff:", self.cutoff_input)
        
        self.percentile_input = QDoubleSpinBox()
        self.percentile_input.setRange(0.80, 0.99)
        self.percentile_input.setValue(DEFAULT_TOP_PERCENTILE)
        self.percentile_input.setSingleStep(0.01)
        self.percentile_input.setDecimals(2)
        self.percentile_input.setMinimumHeight(32)
        params_layout.addRow("Hub Percentile:", self.percentile_input)
        params_group.setLayout(params_layout)
        layout.addWidget(params_group)
        
        # PDB Files Group
        file_group = QGroupBox("PDB Files")
        file_layout = QVBoxLayout()
        file_layout.setSpacing(10)
        file_layout.setContentsMargins(16, 24, 16, 16)
        
        self.file_list = QListWidget()
        self.file_list.setMinimumHeight(150)
        self.file_list.setAlternatingRowColors(True)
        file_layout.addWidget(self.file_list)
        
        file_btn_layout = QHBoxLayout()
        file_btn_layout.setSpacing(8)
        add_files_btn = QPushButton("📄  Add Files")
        add_files_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        add_files_btn.clicked.connect(self.add_files)
        add_folder_btn = QPushButton("📁  Add Folder")
        add_folder_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        add_folder_btn.clicked.connect(self.add_folder)
        clear_btn = QPushButton("✕  Clear")
        clear_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        clear_btn.clicked.connect(self.file_list.clear)
        file_btn_layout.addWidget(add_files_btn)
        file_btn_layout.addWidget(add_folder_btn)
        file_btn_layout.addWidget(clear_btn)
        file_layout.addLayout(file_btn_layout)
        file_group.setLayout(file_layout)
        layout.addWidget(file_group)
        
        # Control Group
        control_group = QGroupBox("Control")
        control_layout = QVBoxLayout()
        control_layout.setSpacing(10)
        control_layout.setContentsMargins(16, 24, 16, 16)
        
        self.run_btn = QPushButton("▶  Run Analysis")
        self.run_btn.setObjectName("successButton")
        self.run_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.run_btn.clicked.connect(self.run_analysis)
        control_layout.addWidget(self.run_btn)
        
        self.stop_btn = QPushButton("■  Stop")
        self.stop_btn.setObjectName("dangerButton")
        self.stop_btn.setEnabled(False)
        self.stop_btn.clicked.connect(self.stop_analysis)
        control_layout.addWidget(self.stop_btn)
        control_group.setLayout(control_layout)
        layout.addWidget(control_group)
        
        # Progress section with subtle styling
        progress_group = QGroupBox("Progress")
        progress_layout = QVBoxLayout()
        progress_layout.setSpacing(8)
        progress_layout.setContentsMargins(16, 24, 16, 16)
        
        self.progress_bar = QProgressBar()
        self.progress_bar.setMinimumHeight(22)
        self.progress_label = QLabel("Ready")
        self.progress_label.setStyleSheet("color: #a0a0a0; font-size: 9pt;")
        progress_layout.addWidget(self.progress_bar)
        progress_layout.addWidget(self.progress_label)
        progress_group.setLayout(progress_layout)
        layout.addWidget(progress_group)
        
        layout.addStretch()
        return panel
    
    def create_right_panel(self) -> QWidget:
        panel = QWidget()
        layout = QVBoxLayout(panel)
        layout.setSpacing(12)
        layout.setContentsMargins(12, 0, 0, 0)
        
        results_group = QGroupBox("Analysis Results")
        results_layout = QVBoxLayout()
        results_layout.setSpacing(8)
        results_layout.setContentsMargins(16, 24, 16, 16)
        
        self.results_list = QListWidget()
        self.results_list.setMinimumHeight(100)
        self.results_list.setAlternatingRowColors(True)
        self.results_list.itemClicked.connect(lambda item: self.load_results(item.text()))
        results_layout.addWidget(self.results_list)
        results_group.setLayout(results_layout)
        layout.addWidget(results_group, stretch=1)
        
        self.result_tabs = QTabWidget()
        self.summary_tab = QTextEdit()
        self.summary_tab.setReadOnly(True)
        self.result_tabs.addTab(self.summary_tab, "📝  Summary")
        
        self.data_tab = QTableWidget()
        self.data_tab.setAlternatingRowColors(True)
        self.result_tabs.addTab(self.data_tab, "📋  Betweenness Data")
        
        self.hub_tab = QTextEdit()
        self.hub_tab.setReadOnly(True)
        self.result_tabs.addTab(self.hub_tab, "🎯  Hub Residues")
        
        self.plot_2d_cb = QWebEngineView()
        self.result_tabs.addTab(self.plot_2d_cb, "📈  2D CB Plot")
        
        self.plot_2d_hist = QWebEngineView()
        self.result_tabs.addTab(self.plot_2d_hist, "📊  2D Histogram")
        
        self.plot_3d_cb = QWebEngineView()
        self.result_tabs.addTab(self.plot_3d_cb, "🔮  3D Network (CB)")
        
        self.plot_3d_spectral = QWebEngineView()
        self.result_tabs.addTab(self.plot_3d_spectral, "✨  3D Network (Spectral)")
        
        layout.addWidget(self.result_tabs, stretch=3)
        return panel
    
    def create_validation_tab(self) -> QWidget:
        tab = QWidget()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        
        content_widget = QWidget()
        layout = QVBoxLayout(content_widget)
        layout.setSpacing(10)
        layout.setContentsMargins(15, 15, 15, 15)
        
        title_label = QLabel("✓  Automatic Validation Engine")
        title_label.setObjectName("titleLabel")
        title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title_label)
        
        input_group = QGroupBox("Input Files")
        input_layout = QFormLayout()
        
        self.val_main_path = QLineEdit()
        self.val_main_path.setPlaceholderText("Select main protein structure")
        main_browse = QPushButton("Browse...")
        main_browse.clicked.connect(lambda: self._browse_file(self.val_main_path, "PDB Files (*.pdb *.cif)"))
        main_h = QHBoxLayout()
        main_h.addWidget(self.val_main_path)
        main_h.addWidget(main_browse)
        input_layout.addRow("Main Structure:", main_h)
        
        self.val_allo_path = QLineEdit()
        self.val_allo_path.setPlaceholderText("Select allosteric region PDB")
        allo_browse = QPushButton("Browse...")
        allo_browse.clicked.connect(lambda: self._browse_file(self.val_allo_path, "PDB Files (*.pdb)"))
        allo_h = QHBoxLayout()
        allo_h.addWidget(self.val_allo_path)
        allo_h.addWidget(allo_browse)
        input_layout.addRow("Allosteric Region:", allo_h)
        
        self.val_orto_path = QLineEdit()
        self.val_orto_path.setPlaceholderText("Optional - Leave empty for auto-detection")
        orto_browse = QPushButton("Browse...")
        orto_browse.clicked.connect(lambda: self._browse_file(self.val_orto_path, "PDB Files (*.pdb)"))
        orto_h = QHBoxLayout()
        orto_h.addWidget(self.val_orto_path)
        orto_h.addWidget(orto_browse)
        input_layout.addRow("Orthosteric Region:", orto_h)
        
        self.val_top5_path = QLineEdit()
        self.val_top5_path.setPlaceholderText("Select top_5_percent.out from RIN analysis")
        top5_browse = QPushButton("Browse...")
        top5_browse.clicked.connect(lambda: self._browse_file(self.val_top5_path, "Output Files (*.out)"))
        top5_h = QHBoxLayout()
        top5_h.addWidget(self.val_top5_path)
        top5_h.addWidget(top5_browse)
        input_layout.addRow("Top 5% Hubs:", top5_h)
        
        input_group.setLayout(input_layout)
        layout.addWidget(input_group)
        
        self.val_run_btn = QPushButton("▶  Run Validation")
        self.val_run_btn.setObjectName("validationButton")
        self.val_run_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.val_run_btn.clicked.connect(self.run_validation)
        layout.addWidget(self.val_run_btn)
        
        self.val_progress_bar = QProgressBar()
        self.val_progress_label = QLabel("Ready")
        layout.addWidget(self.val_progress_bar)
        layout.addWidget(self.val_progress_label)
        
        results_label = QLabel("📈  Validation Results (4 Analyses)")
        results_label.setObjectName("subtitleLabel")
        results_label.setStyleSheet("font-size: 14pt; font-weight: bold; color: #2979ff; padding: 8px 0; margin-top: 8px;")
        layout.addWidget(results_label)
        
        matrix_grid = QGridLayout()
        self.val_allo_core_widget = self.create_confusion_matrix_widget()
        self.val_allo_5a_widget = self.create_confusion_matrix_widget()
        self.val_orto_core_widget = self.create_confusion_matrix_widget()
        self.val_orto_5a_widget = self.create_confusion_matrix_widget()
        
        matrix_grid.addWidget(self._wrap_in_group(self.val_allo_core_widget, "1. Allosteric Core"), 0, 0)
        matrix_grid.addWidget(self._wrap_in_group(self.val_allo_5a_widget, "2. Allosteric 5Å"), 0, 1)
        matrix_grid.addWidget(self._wrap_in_group(self.val_orto_core_widget, "3. Orthosteric Core"), 1, 0)
        matrix_grid.addWidget(self._wrap_in_group(self.val_orto_5a_widget, "4. Orthosteric 5Å"), 1, 1)
        layout.addLayout(matrix_grid)
        
        export_layout = QHBoxLayout()
        export_csv = QPushButton("Export Results (CSV)")
        export_csv.clicked.connect(self.export_validation_results)
        export_zones = QPushButton("Export Zone Data")
        export_zones.clicked.connect(self.export_zone_data)
        export_pymol = QPushButton("Export PyMOL Script")
        export_pymol.clicked.connect(self.export_pymol_session)
        export_layout.addWidget(export_csv)
        export_layout.addWidget(export_zones)
        export_layout.addWidget(export_pymol)
        layout.addLayout(export_layout)
        
        scroll.setWidget(content_widget)
        tab_layout = QVBoxLayout(tab)
        tab_layout.setContentsMargins(0, 0, 0, 0)
        tab_layout.addWidget(scroll)
        return tab
    
    def create_pocket_detection_tab(self) -> QWidget:
        tab = QWidget()
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        
        content_widget = QWidget()
        layout = QVBoxLayout(content_widget)
        layout.setSpacing(10)
        layout.setContentsMargins(15, 15, 15, 15)
        
        title_label = QLabel("🔬  Pocket Detection & Consensus Scoring")
        title_label.setObjectName("titleLabel")
        title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title_label)
        
        tool_group = QGroupBox("Tool Configuration")
        tool_layout = QFormLayout()
        
        self.pocket_tool_combo = QComboBox()
        self.pocket_tool_combo.addItems(["P2Rank (Recommended)", "fpocket"])
        tool_layout.addRow("Detection Tool:", self.pocket_tool_combo)
        
        self.pocket_tool_path = QLineEdit()
        self.pocket_tool_path.setPlaceholderText("Path to P2Rank directory or fpocket executable")
        tool_browse = QPushButton("Browse...")
        tool_browse.clicked.connect(self._browse_pocket_tool)
        tool_h = QHBoxLayout()
        tool_h.addWidget(self.pocket_tool_path)
        tool_h.addWidget(tool_browse)
        tool_layout.addRow("Tool Path:", tool_h)
        tool_group.setLayout(tool_layout)
        layout.addWidget(tool_group)
        
        input_group = QGroupBox("Input Data")
        input_layout = QFormLayout()
        
        self.pocket_main_path = QLineEdit()
        self.pocket_main_path.setPlaceholderText("Select main protein structure")
        struct_browse = QPushButton("Browse...")
        struct_browse.clicked.connect(lambda: self._browse_file(self.pocket_main_path, "PDB Files (*.pdb *.cif)"))
        struct_h = QHBoxLayout()
        struct_h.addWidget(self.pocket_main_path)
        struct_h.addWidget(struct_browse)
        input_layout.addRow("Main Structure:", struct_h)
        
        self.pocket_hub_path = QLineEdit()
        self.pocket_hub_path.setPlaceholderText("Select top_5_percent.out")
        hub_browse = QPushButton("Browse...")
        hub_browse.clicked.connect(lambda: self._browse_file(self.pocket_hub_path, "Output Files (*.out)"))
        hub_h = QHBoxLayout()
        hub_h.addWidget(self.pocket_hub_path)
        hub_h.addWidget(hub_browse)
        input_layout.addRow("Hub Residues:", hub_h)
        
        self.use_validation_check = QCheckBox("Use validation data from Tab 2")
        self.use_validation_check.setChecked(True)
        input_layout.addRow("", self.use_validation_check)
        input_group.setLayout(input_layout)
        layout.addWidget(input_group)
        
        scoring_group = QGroupBox("Scoring Parameters")
        scoring_layout = QGridLayout()
        
        scoring_layout.addWidget(QLabel("Geometric Weight:"), 0, 0)
        self.weight_geo_slider = QSlider(Qt.Orientation.Horizontal)
        self.weight_geo_slider.setRange(0, 100)
        self.weight_geo_slider.setValue(30)  # Reduced: geometry alone isn't enough
        self.weight_geo_label = QLabel("0.30")
        self.weight_geo_slider.valueChanged.connect(lambda v: self.weight_geo_label.setText(f"{v/100:.2f}"))
        scoring_layout.addWidget(self.weight_geo_slider, 0, 1)
        scoring_layout.addWidget(self.weight_geo_label, 0, 2)
        
        scoring_layout.addWidget(QLabel("Hub Impact Weight:"), 1, 0)  # Renamed from "Hub Density"
        self.weight_hub_slider = QSlider(Qt.Orientation.Horizontal)
        self.weight_hub_slider.setRange(0, 100)
        self.weight_hub_slider.setValue(50)  # Increased: hubs are the key signal
        self.weight_hub_label = QLabel("0.50")
        self.weight_hub_slider.valueChanged.connect(lambda v: self.weight_hub_label.setText(f"{v/100:.2f}"))
        scoring_layout.addWidget(self.weight_hub_slider, 1, 1)
        scoring_layout.addWidget(self.weight_hub_label, 1, 2)
        
        scoring_layout.addWidget(QLabel("Validation Weight:"), 2, 0)
        self.weight_val_slider = QSlider(Qt.Orientation.Horizontal)
        self.weight_val_slider.setRange(0, 100)
        self.weight_val_slider.setValue(20)
        self.weight_val_label = QLabel("0.20")
        self.weight_val_slider.valueChanged.connect(lambda v: self.weight_val_label.setText(f"{v/100:.2f}"))
        scoring_layout.addWidget(self.weight_val_slider, 2, 1)
        scoring_layout.addWidget(self.weight_val_label, 2, 2)
        
        scoring_layout.addWidget(QLabel("Allosteric Boost:"), 3, 0)
        self.boost_allo_spin = QDoubleSpinBox()
        self.boost_allo_spin.setRange(0, 1.0)
        self.boost_allo_spin.setValue(0.50)
        self.boost_allo_spin.setSingleStep(0.05)
        scoring_layout.addWidget(self.boost_allo_spin, 3, 1)
        
        scoring_layout.addWidget(QLabel("Orthosteric Boost:"), 4, 0)
        self.boost_orto_spin = QDoubleSpinBox()
        self.boost_orto_spin.setRange(0, 1.0)
        self.boost_orto_spin.setValue(0.50)
        self.boost_orto_spin.setSingleStep(0.05)
        scoring_layout.addWidget(self.boost_orto_spin, 4, 1)
        
        scoring_group.setLayout(scoring_layout)
        layout.addWidget(scoring_group)
        
        self.pocket_run_btn = QPushButton("▶  Run Pocket Detection")
        self.pocket_run_btn.setObjectName("pocketButton")
        self.pocket_run_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.pocket_run_btn.clicked.connect(self.run_pocket_detection)
        layout.addWidget(self.pocket_run_btn)
        
        self.pocket_progress_bar = QProgressBar()
        self.pocket_progress_label = QLabel("Ready")
        layout.addWidget(self.pocket_progress_bar)
        layout.addWidget(self.pocket_progress_label)
        
        results_label = QLabel("📊  Pocket Results")
        results_label.setObjectName("subtitleLabel")
        results_label.setStyleSheet("font-size: 14pt; font-weight: bold; color: #2979ff; padding: 8px 0; margin-top: 8px;")
        layout.addWidget(results_label)
        
        self.pocket_results_table = QTableWidget()
        self.pocket_results_table.setMinimumHeight(200)
        self.pocket_results_table.setAlternatingRowColors(True)
        layout.addWidget(self.pocket_results_table)
        
        export_layout = QHBoxLayout()
        export_csv = QPushButton("Export CSV")
        export_csv.clicked.connect(self.export_pocket_results)
        export_pymol = QPushButton("Export PyMOL")
        export_pymol.clicked.connect(self.export_pocket_pymol)
        export_layout.addWidget(export_csv)
        export_layout.addWidget(export_pymol)
        layout.addLayout(export_layout)
        layout.addStretch()
        
        scroll.setWidget(content_widget)
        tab_layout = QVBoxLayout(tab)
        tab_layout.setContentsMargins(0, 0, 0, 0)
        tab_layout.addWidget(scroll)
        return tab
    
    def _wrap_in_group(self, widget: QWidget, title: str) -> QGroupBox:
        group = QGroupBox(title)
        layout = QVBoxLayout()
        layout.addWidget(widget)
        group.setLayout(layout)
        return group
    
    def create_confusion_matrix_widget(self) -> QWidget:
        widget = QWidget()
        layout = QVBoxLayout(widget)
        layout.setSpacing(12)
        
        matrix_group = QGroupBox("Confusion Matrix")
        matrix_layout = QGridLayout()
        matrix_layout.setSpacing(8)
        matrix_layout.setContentsMargins(12, 20, 12, 12)
        matrix_layout.addWidget(QLabel(""), 0, 0)
        
        # Header labels with dark theme styling
        for text, col in [("Predicted +", 1), ("Predicted −", 2)]:
            lbl = QLabel(text)
            lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            lbl.setStyleSheet("font-weight: bold; color: #2979ff; font-size: 10pt;")
            matrix_layout.addWidget(lbl, 0, col)
        
        for i, text in enumerate(["Actual +", "Actual −"]):
            lbl = QLabel(text)
            lbl.setStyleSheet("font-weight: bold; color: #2979ff; font-size: 10pt;")
            matrix_layout.addWidget(lbl, i + 1, 0)
        
        # Matrix cells with dark theme colors
        tp_cell = self._create_matrix_cell("TP: 0", "#00897b")  # Teal for True Positive
        fp_cell = self._create_matrix_cell("FP: 0", "#c62828")  # Red for False Positive
        fn_cell = self._create_matrix_cell("FN: 0", "#c62828")  # Red for False Negative
        tn_cell = self._create_matrix_cell("TN: 0", "#00897b")  # Teal for True Negative
        
        matrix_layout.addWidget(tp_cell, 1, 1)
        matrix_layout.addWidget(fp_cell, 2, 1)
        matrix_layout.addWidget(fn_cell, 1, 2)
        matrix_layout.addWidget(tn_cell, 2, 2)
        
        setattr(widget, 'tp_cell', tp_cell)
        setattr(widget, 'fp_cell', fp_cell)
        setattr(widget, 'fn_cell', fn_cell)
        setattr(widget, 'tn_cell', tn_cell)
        
        matrix_group.setLayout(matrix_layout)
        layout.addWidget(matrix_group)
        
        metrics_group = QGroupBox("Performance Metrics")
        metrics_layout = QFormLayout()
        metrics_layout.setSpacing(10)
        metrics_layout.setContentsMargins(12, 20, 12, 12)
        
        # Styled metric labels
        metric_names = {
            'precision_lbl': ('Precision', '📊'),
            'recall_lbl': ('Recall', '🎯'),
            'f1_lbl': ('F1 Score', '⚡'),
            'accuracy_lbl': ('Accuracy', '✓'),
            'specificity_lbl': ('Specificity', '🔬')
        }
        
        for attr_name, (display_name, icon) in metric_names.items():
            lbl = QLabel("0.000")
            lbl.setStyleSheet("font-size: 11pt; font-weight: bold; color: #e0e0e0; padding: 4px;")
            setattr(widget, attr_name, lbl)
            row_label = QLabel(f"{display_name}:")
            row_label.setStyleSheet("font-size: 10pt; color: #a0a0a0;")
            metrics_layout.addRow(row_label, lbl)
        
        metrics_group.setLayout(metrics_layout)
        layout.addWidget(metrics_group)
        return widget
    
    def _create_matrix_cell(self, text: str, color: str) -> QLabel:
        """Create a styled confusion matrix cell for the dark theme."""
        cell = QLabel(text)
        cell.setAlignment(Qt.AlignmentFlag.AlignCenter)
        cell.setStyleSheet(f"""
            QLabel {{
                background-color: {color};
                color: white;
                font-size: 13pt;
                font-weight: bold;
                padding: 18px;
                border-radius: 6px;
                min-width: 110px;
                min-height: 65px;
                border: 1px solid rgba(255, 255, 255, 0.1);
            }}
        """)
        return cell
    
    def add_files(self):
        files, _ = QFileDialog.getOpenFileNames(self, "Select PDB Files", "", "PDB Files (*.pdb *.cif)")
        for f in files:
            self.file_list.addItem(f)
    
    def add_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Folder")
        if folder:
            for ext in ['*.pdb', '*.cif']:
                for f in glob.glob(os.path.join(folder, ext)):
                    self.file_list.addItem(f)
    
    def _browse_file(self, line_edit: QLineEdit, file_filter: str):
        filename, _ = QFileDialog.getOpenFileName(self, "Select File", "", file_filter)
        if filename:
            line_edit.setText(filename)
    
    def _browse_pocket_tool(self):
        if self.pocket_tool_combo.currentIndex() == 0:
            folder = QFileDialog.getExistingDirectory(self, "Select P2Rank Directory")
            if folder:
                self.pocket_tool_path.setText(folder)
        else:
            filename, _ = QFileDialog.getOpenFileName(self, "Select fpocket", "", "All Files (*)")
            if filename:
                self.pocket_tool_path.setText(filename)
    
    def run_analysis(self):
        if self.file_list.count() == 0:
            QMessageBox.warning(self, "No Files", "Please add PDB files first")
            return
        
        pdb_files = [self.file_list.item(i).text() for i in range(self.file_list.count())]
        Path(self.output_dir).mkdir(parents=True, exist_ok=True)
        
        self.analysis_thread = AnalysisThread(pdb_files, self.output_dir, self.cutoff_input.value(), self.percentile_input.value())
        self.analysis_thread.progress_update.connect(lambda p, m: (self.progress_bar.setValue(p), self.progress_label.setText(m)))
        self.analysis_thread.single_pdb_complete.connect(lambda pdb_id, r: (self.current_results.update({pdb_id: r}), self.results_list.addItem(pdb_id)))
        self.analysis_thread.analysis_complete.connect(lambda r: (self.run_btn.setEnabled(True), self.stop_btn.setEnabled(False), QMessageBox.information(self, "Complete", f"Analysis completed for {len(r)} PDB(s)")))
        self.analysis_thread.error_occurred.connect(lambda e: QMessageBox.critical(self, "Error", e))
        
        self.run_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)
        self.analysis_thread.start()
    
    def stop_analysis(self):
        if self.analysis_thread:
            self.analysis_thread.stop()
            self.analysis_thread.wait()
            self.run_btn.setEnabled(True)
            self.stop_btn.setEnabled(False)
            self.progress_label.setText("Stopped")
    
    def load_results(self, pdb_id: str):
        if pdb_id not in self.current_results:
            return
        results = self.current_results[pdb_id]
        
        if "error" in results:
            self.summary_tab.setText(f"Error: {results['error']}")
            return
        
        self.summary_tab.setText(f"PDB ID: {results['pdb_id']}\nStatus: {results['status']}\nResidues: {results.get('num_residues', 'N/A')}\nContacts: {results.get('num_contacts', 'N/A')}\nHubs: {len(results.get('hub_residues', []))}")
        
        if 'hub_residues' in results:
            self.hub_tab.setText("Hub Residues:\n\n" + ", ".join(map(str, results['hub_residues'])))
        
        if 'files' in results:
            files = results['files']
            for attr, key in [(self.plot_2d_cb, 'plot_2d_cb_vs_residue'), (self.plot_2d_hist, 'plot_2d_cb_histogram'),
                              (self.plot_3d_cb, 'plot_3d_network_cb'), (self.plot_3d_spectral, 'plot_3d_network_spectral')]:
                if key in files and Path(files[key]).exists():
                    QTimer.singleShot(100, lambda w=attr, p=files[key]: w.setUrl(QUrl.fromLocalFile(str(Path(p).resolve()))))
    
    def run_validation(self):
        if not all([self.val_main_path.text(), self.val_allo_path.text(), self.val_top5_path.text()]):
            QMessageBox.warning(self, "Missing Input", "Please fill in required fields")
            return
        
        self.validation_thread = ValidationThread(self.val_main_path.text(), self.val_allo_path.text(), self.val_orto_path.text(), self.val_top5_path.text())
        self.validation_thread.progress_update.connect(lambda p, m: (self.val_progress_bar.setValue(p), self.val_progress_label.setText(m)))
        self.validation_thread.validation_complete.connect(self.on_validation_complete)
        self.validation_thread.error_occurred.connect(lambda e: (self.val_run_btn.setEnabled(True), QMessageBox.critical(self, "Error", e)))
        
        self.val_run_btn.setEnabled(False)
        self.validation_thread.start()
    
    def on_validation_complete(self, results: dict):
        self.validation_results = results
        self.val_run_btn.setEnabled(True)
        
        for widget, key in [(self.val_allo_core_widget, 'allo_core'), (self.val_allo_5a_widget, 'allo_5a'),
                            (self.val_orto_core_widget, 'orto_core'), (self.val_orto_5a_widget, 'orto_5a')]:
            r = results[key]
            widget.tp_cell.setText(f"TP: {r['TP']}")
            widget.fp_cell.setText(f"FP: {r['FP']}")
            widget.fn_cell.setText(f"FN: {r['FN']}")
            widget.tn_cell.setText(f"TN: {r['TN']}")
            widget.precision_lbl.setText(f"{r['precision']:.3f}")
            widget.recall_lbl.setText(f"{r['recall']:.3f}")
            widget.f1_lbl.setText(f"{r['f1_score']:.3f}")
            widget.accuracy_lbl.setText(f"{r['accuracy']:.3f}")
            widget.specificity_lbl.setText(f"{r['specificity']:.3f}")
        
        m = results['metadata']
        QMessageBox.information(self, "Complete", f"Universe: {m['universe_count']}\nHubs: {m['hub_count']}\nAllo Core: {m['T_Allo_Core_count']}\nOrto Core: {m['T_Orto_Core_count']}")
    
    def export_validation_results(self):
        if not self.validation_results:
            QMessageBox.warning(self, "No Results", "Run validation first")
            return
        filename, _ = QFileDialog.getSaveFileName(self, "Save Results", "validation_results.csv", "CSV (*.csv)")
        if filename:
            # Verileri listeye topla
            data = []
            for name, key in [('Allo Core', 'allo_core'), ('Allo 5A', 'allo_5a'), ('Orto Core', 'orto_core'), ('Orto 5A', 'orto_5a')]:
                r = self.validation_results[key]
                data.append({
                    'Analysis': name,
                    'TP': r['TP'], 'FP': r['FP'], 'FN': r['FN'], 'TN': r['TN'],
                    'Precision': r['precision'],
                    'Recall': r['recall'],
                    'F1': r['f1_score'],
                    'Accuracy': r['accuracy'],
                    'Specificity': r['specificity']
                })
            
            # DataFrame oluştur ve Türkçe formatla kaydet
            df = pd.DataFrame(data)
            df.to_csv(filename, index=False, sep=';', decimal=',')
            QMessageBox.information(self, "Saved", f"Saved to {filename}")
    
    def export_zone_data(self):
        if not self.validation_results:
            QMessageBox.warning(self, "No Results", "Run validation first")
            return
        filename, _ = QFileDialog.getSaveFileName(self, "Save Zone Data", "zone_data.csv", "CSV (*.csv)")
        if filename:
            with open(filename, 'w', encoding='utf-8-sig') as f: # utf-8-sig Türkçe karakterler için
                for zone_name, residues in self.validation_results['zone_data'].items():
                    f.write(f"\n# {zone_name} ({len(residues)} residues)\nChain;ResID\n") # Virgül yerine ;
                    for chain, resid in residues:
                        f.write(f"{chain};{resid}\n") # Virgül yerine ;
            QMessageBox.information(self, "Saved", f"Saved to {filename}")
    
    def export_pymol_session(self):
        if not self.validation_results:
            QMessageBox.warning(self, "No Results", "Run validation first")
            return
        filename, _ = QFileDialog.getSaveFileName(self, "Save PyMOL Script", "validation.pml", "PyMOL (*.pml)")
        if filename:
            main_file = str(Path(self.val_main_path.text()).resolve()).replace('\\', '/')
            generator = ValidationPyMOLGenerator(main_file)
            script = generator.generate_script(self.validation_results, self.val_allo_path.text(), self.val_orto_path.text())
            with open(filename, 'w') as f:
                f.write(script)
            QMessageBox.information(self, "Saved", f"Publication-quality PyMOL script saved to {filename}")
    
    def run_pocket_detection(self):
        if not all([self.pocket_tool_path.text(), self.pocket_main_path.text(), self.pocket_hub_path.text()]):
            QMessageBox.warning(self, "Missing Input", "Please fill in required fields")
            return
        
        hub_residues = set()
        try:
            with open(self.pocket_hub_path.text(), 'r') as f:
                for i, line in enumerate(f):
                    if i == 0 or not line.strip():
                        continue
                    parts = line.strip().split()
                    if len(parts) >= 3:
                        try:
                            hub_residues.add((parts[2].strip(), int(parts[0])))
                        except:
                            pass
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to load hubs: {e}")
            return
        
        self.pocket_config.tool = PocketTool.P2RANK if self.pocket_tool_combo.currentIndex() == 0 else PocketTool.FPOCKET
        self.pocket_config.tool_path = self.pocket_tool_path.text()
        self.pocket_config.weight_geometric = self.weight_geo_slider.value() / 100.0
        self.pocket_config.weight_hub_impact = self.weight_hub_slider.value() / 100.0  # Updated field name
        self.pocket_config.weight_validation = self.weight_val_slider.value() / 100.0
        self.pocket_config.boost_allosteric = self.boost_allo_spin.value()
        self.pocket_config.boost_orthosteric = self.boost_orto_spin.value()
        
        validation_data = self.validation_results if self.use_validation_check.isChecked() and self.validation_results else None
        
        self.pocket_thread = PocketDetectionThread(self.pocket_config, self.pocket_main_path.text(), hub_residues, validation_data, str(Path(self.output_dir) / "pocket_detection"))
        self.pocket_thread.progress_update.connect(lambda p, m: (self.pocket_progress_bar.setValue(p), self.pocket_progress_label.setText(m)))
        self.pocket_thread.detection_complete.connect(self.on_pocket_complete)
        self.pocket_thread.error_occurred.connect(lambda e: (self.pocket_run_btn.setEnabled(True), QMessageBox.critical(self, "Error", e)))
        
        self.pocket_run_btn.setEnabled(False)
        self.pocket_thread.start()
    
    def on_pocket_complete(self, results: dict):
        self.pocket_results = results
        self.pocket_run_btn.setEnabled(True)
        
        report_df = results['report']
        self.pocket_results_table.setRowCount(len(report_df))
        self.pocket_results_table.setColumnCount(len(report_df.columns))
        self.pocket_results_table.setHorizontalHeaderLabels(report_df.columns.tolist())
        
        for i, row in report_df.iterrows():
            for j, col in enumerate(report_df.columns):
                self.pocket_results_table.setItem(i, j, QTableWidgetItem(str(row[col])))
        
        self.pocket_results_table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        QMessageBox.information(self, "Complete", f"Found {len(results['pockets'])} pockets using {results['tool_used']}")
    
    def export_pocket_results(self):
        if not self.pocket_results:
            QMessageBox.warning(self, "No Results", "Run pocket detection first")
            return
        filename, _ = QFileDialog.getSaveFileName(self, "Save Results", "pocket_results.csv", "CSV (*.csv)")
        if filename:
            # DÜZELTME: Türkçe Excel formatı için (sep=';', decimal=',') eklendi
            self.pocket_results['report'].to_csv(filename, index=False, sep=';', decimal=',')
            QMessageBox.information(self, "Saved", f"Saved to {filename}")
    
    def export_pocket_pymol(self):
        if not self.pocket_results:
            QMessageBox.warning(self, "No Results", "Run pocket detection first")
            return
        filename, _ = QFileDialog.getSaveFileName(self, "Save PyMOL Script", "pocket_visualization.pml", "PyMOL (*.pml)")
        if filename:
            with open(filename, 'w') as f:
                f.write(self.pocket_results['pymol_script'])
            QMessageBox.information(self, "Saved", f"Publication-quality PyMOL script saved to {filename}")
    
    def create_menu_bar(self):
        menubar = self.menuBar()
        file_menu = menubar.addMenu("File")
        exit_action = QAction("Exit", self)
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)
        
        help_menu = menubar.addMenu("Help")
        about_action = QAction("About", self)
        about_action.triggered.connect(self.show_about)
        help_menu.addAction(about_action)
    
    def create_status_bar(self):
        self.statusBar().showMessage(f"Ready | Platform: {self.platform_helper.platform.value.capitalize()}")
    
    def show_about(self):
        QMessageBox.about(self, "About RIN Analyzer", f"{APP_NAME} v{APP_VERSION}\n\nLigand-Free Edition\nPublication-Quality PyMOL Visualization\n\nFeatures:\n- Core zones as solid surfaces\n- Shell zones (5Å) as mesh\n- Hub overlap color-coding\n- Ray tracing ready")
    
    def setup_style(self):
        """
        Scientific Chic Dark Theme
        Design Philosophy: High-end scientific software aesthetic (Schrödinger Maestro, PyMOL 3.0)
        Palette: Deep charcoal backgrounds, off-white text, muted Electric Blue accent
        """
        # Define theme colors as constants for consistency
        ACCENT_COLOR = "#2979ff"  # Electric Blue - primary accent
        ACCENT_HOVER = "#448aff"  # Lighter blue for hover states
        ACCENT_PRESSED = "#1565c0"  # Darker blue for pressed states
        
        BG_WINDOW = "#1e1e1e"  # Main window background
        BG_SURFACE = "#2b2b2b"  # Elevated surfaces (panels, cards)
        BG_INPUT = "#121212"  # Input fields, darker than window
        BG_HOVER = "#3a3a3a"  # Hover state for surfaces
        
        BORDER_DEFAULT = "#3e3e3e"  # Subtle borders
        BORDER_LIGHT = "#4a4a4a"  # Lighter borders for emphasis
        
        TEXT_PRIMARY = "#e0e0e0"  # Primary text (Gray 90%)
        TEXT_SECONDARY = "#a0a0a0"  # Secondary/muted text
        TEXT_DISABLED = "#606060"  # Disabled text
        
        # Success/Warning/Error colors for confusion matrix
        COLOR_SUCCESS = "#00c853"  # Green for TP/TN
        COLOR_WARNING = "#ff9100"  # Orange for FP/FN
        COLOR_ERROR = "#ff5252"  # Red for errors
        
        self.setStyleSheet(f"""
            /* ═══════════════════════════════════════════════════════════════
               GLOBAL WINDOW & CONTAINERS
               ═══════════════════════════════════════════════════════════════ */
            QMainWindow {{
                background-color: {BG_WINDOW};
                color: {TEXT_PRIMARY};
            }}
            
            QWidget {{
                background-color: {BG_WINDOW};
                color: {TEXT_PRIMARY};
                font-family: "Segoe UI", "SF Pro Display", "Roboto", "Helvetica Neue", sans-serif;
                font-size: 10pt;
            }}
            
            QSplitter::handle {{
                background-color: {BORDER_DEFAULT};
                width: 2px;
                height: 2px;
            }}
            
            QSplitter::handle:hover {{
                background-color: {ACCENT_COLOR};
            }}

            /* ═══════════════════════════════════════════════════════════════
               INPUT FIELDS (QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox)
               ═══════════════════════════════════════════════════════════════ */
            QLineEdit, QSpinBox, QDoubleSpinBox {{
                background-color: {BG_INPUT};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 6px 10px;
                color: {TEXT_PRIMARY};
                selection-background-color: {ACCENT_COLOR};
                selection-color: white;
            }}
            
            QLineEdit:focus, QSpinBox:focus, QDoubleSpinBox:focus {{
                border: 1px solid {ACCENT_COLOR};
                outline: none;
            }}
            
            QLineEdit:disabled, QSpinBox:disabled, QDoubleSpinBox:disabled {{
                background-color: {BG_SURFACE};
                color: {TEXT_DISABLED};
                border: 1px solid {BORDER_DEFAULT};
            }}
            
            QLineEdit::placeholder {{
                color: {TEXT_SECONDARY};
            }}
            
            /* Spin box buttons */
            QSpinBox::up-button, QDoubleSpinBox::up-button,
            QSpinBox::down-button, QDoubleSpinBox::down-button {{
                background-color: {BG_SURFACE};
                border: none;
                border-left: 1px solid {BORDER_DEFAULT};
                width: 20px;
            }}
            
            QSpinBox::up-button:hover, QDoubleSpinBox::up-button:hover,
            QSpinBox::down-button:hover, QDoubleSpinBox::down-button:hover {{
                background-color: {BG_HOVER};
            }}
            
            QSpinBox::up-arrow, QDoubleSpinBox::up-arrow {{
                image: none;
                border-left: 4px solid transparent;
                border-right: 4px solid transparent;
                border-bottom: 5px solid {TEXT_PRIMARY};
                width: 0;
                height: 0;
            }}
            
            QSpinBox::down-arrow, QDoubleSpinBox::down-arrow {{
                image: none;
                border-left: 4px solid transparent;
                border-right: 4px solid transparent;
                border-top: 5px solid {TEXT_PRIMARY};
                width: 0;
                height: 0;
            }}
            
            /* ComboBox */
            QComboBox {{
                background-color: {BG_INPUT};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 6px 10px;
                padding-right: 30px;
                color: {TEXT_PRIMARY};
                min-height: 20px;
            }}
            
            QComboBox:focus, QComboBox:on {{
                border: 1px solid {ACCENT_COLOR};
            }}
            
            QComboBox::drop-down {{
                subcontrol-origin: padding;
                subcontrol-position: right center;
                width: 24px;
                border: none;
                border-left: 1px solid {BORDER_DEFAULT};
                background-color: {BG_SURFACE};
                border-top-right-radius: 4px;
                border-bottom-right-radius: 4px;
            }}
            
            QComboBox::down-arrow {{
                image: none;
                border-left: 5px solid transparent;
                border-right: 5px solid transparent;
                border-top: 6px solid {TEXT_PRIMARY};
                width: 0;
                height: 0;
            }}
            
            QComboBox QAbstractItemView {{
                background-color: {BG_SURFACE};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 4px;
                selection-background-color: {ACCENT_COLOR};
                selection-color: white;
                outline: none;
            }}
            
            QComboBox QAbstractItemView::item {{
                padding: 6px 10px;
                min-height: 24px;
            }}
            
            QComboBox QAbstractItemView::item:hover {{
                background-color: {BG_HOVER};
            }}

            /* ═══════════════════════════════════════════════════════════════
               BUTTONS (QPushButton)
               ═══════════════════════════════════════════════════════════════ */
            QPushButton {{
                background-color: #3c3c3c;
                color: {TEXT_PRIMARY};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 8px 16px;
                font-weight: 500;
                min-height: 18px;
            }}
            
            QPushButton:hover {{
                background-color: #4a4a4a;
                border-color: {BORDER_LIGHT};
            }}
            
            QPushButton:pressed {{
                background-color: #2d2d2d;
            }}
            
            QPushButton:disabled {{
                background-color: #2d2d2d;
                color: {TEXT_DISABLED};
                border-color: #2d2d2d;
            }}
            
            /* Primary Action Buttons (identified by object name) */
            QPushButton#primaryButton,
            QPushButton[primary="true"] {{
                background-color: {ACCENT_COLOR};
                color: white;
                font-weight: bold;
                font-size: 11pt;
                padding: 12px 24px;
                border: none;
            }}
            
            QPushButton#primaryButton:hover,
            QPushButton[primary="true"]:hover {{
                background-color: {ACCENT_HOVER};
            }}
            
            QPushButton#primaryButton:pressed,
            QPushButton[primary="true"]:pressed {{
                background-color: {ACCENT_PRESSED};
            }}
            
            /* Success Button (Green - for Run/Analyze) */
            QPushButton#successButton {{
                background-color: #00897b;
                color: white;
                font-weight: bold;
                font-size: 11pt;
                padding: 12px 24px;
                border: none;
            }}
            
            QPushButton#successButton:hover {{
                background-color: #00a08a;
            }}
            
            QPushButton#successButton:pressed {{
                background-color: #00695c;
            }}
            
            /* Validation Button (Blue) */
            QPushButton#validationButton {{
                background-color: {ACCENT_COLOR};
                color: white;
                font-weight: bold;
                font-size: 11pt;
                padding: 12px 24px;
                border: none;
            }}
            
            QPushButton#validationButton:hover {{
                background-color: {ACCENT_HOVER};
            }}
            
            /* Pocket Detection Button (Purple/Violet) */
            QPushButton#pocketButton {{
                background-color: #7c4dff;
                color: white;
                font-weight: bold;
                font-size: 11pt;
                padding: 12px 24px;
                border: none;
            }}
            
            QPushButton#pocketButton:hover {{
                background-color: #9e7bff;
            }}
            
            QPushButton#pocketButton:pressed {{
                background-color: #651fff;
            }}
            
            /* Danger/Stop Button */
            QPushButton#dangerButton {{
                background-color: #c62828;
                color: white;
                font-weight: bold;
                border: none;
            }}
            
            QPushButton#dangerButton:hover {{
                background-color: #e53935;
            }}
            
            QPushButton#dangerButton:disabled {{
                background-color: #4a2c2c;
                color: {TEXT_DISABLED};
            }}

            /* ═══════════════════════════════════════════════════════════════
               NAVIGATION (QTabWidget)
               ═══════════════════════════════════════════════════════════════ */
            QTabWidget::pane {{
                background-color: {BG_WINDOW};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                top: -1px;
            }}
            
            QTabBar {{
                background-color: transparent;
            }}
            
            QTabBar::tab {{
                background-color: #2d2d2d;
                color: {TEXT_SECONDARY};
                border: 1px solid {BORDER_DEFAULT};
                border-bottom: none;
                border-top-left-radius: 6px;
                border-top-right-radius: 6px;
                padding: 10px 20px;
                margin-right: 2px;
                font-weight: 500;
            }}
            
            QTabBar::tab:selected {{
                background-color: {BG_WINDOW};
                color: {ACCENT_COLOR};
                border-bottom: 2px solid {ACCENT_COLOR};
                font-weight: bold;
            }}
            
            QTabBar::tab:hover:!selected {{
                background-color: {BG_HOVER};
                color: {TEXT_PRIMARY};
            }}

            /* ═══════════════════════════════════════════════════════════════
               DATA VIEWS (QTableWidget, QListWidget, QTextEdit)
               ═══════════════════════════════════════════════════════════════ */
            QTableWidget, QListWidget {{
                background-color: #1a1a1a;
                alternate-background-color: #222222;
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                gridline-color: #2a2a2a;
                color: {TEXT_PRIMARY};
                selection-background-color: {ACCENT_COLOR};
                selection-color: white;
            }}
            
            QTableWidget::item, QListWidget::item {{
                padding: 8px 12px;
                border-bottom: 1px solid #2a2a2a;
            }}
            
            QTableWidget::item:selected, QListWidget::item:selected {{
                background-color: {ACCENT_COLOR};
                color: white;
            }}
            
            QTableWidget::item:hover, QListWidget::item:hover {{
                background-color: {BG_HOVER};
            }}
            
            /* Table Headers */
            QHeaderView::section {{
                background-color: {BG_SURFACE};
                color: {TEXT_PRIMARY};
                padding: 10px 12px;
                border: none;
                border-bottom: 2px solid {ACCENT_COLOR};
                font-weight: bold;
                font-size: 9pt;
                text-transform: uppercase;
            }}
            
            QHeaderView::section:hover {{
                background-color: {BG_HOVER};
            }}
            
            /* QTextEdit */
            QTextEdit {{
                background-color: #1a1a1a;
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 10px;
                color: {TEXT_PRIMARY};
                selection-background-color: {ACCENT_COLOR};
                selection-color: white;
                font-family: "JetBrains Mono", "Fira Code", "Consolas", monospace;
                font-size: 9pt;
            }}
            
            QTextEdit:focus {{
                border: 1px solid {ACCENT_COLOR};
            }}

            /* ═══════════════════════════════════════════════════════════════
               GROUPING (QGroupBox)
               ═══════════════════════════════════════════════════════════════ */
            QGroupBox {{
                background-color: {BG_SURFACE};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 6px;
                margin-top: 16px;
                padding: 16px;
                padding-top: 24px;
                font-weight: bold;
            }}
            
            QGroupBox::title {{
                subcontrol-origin: margin;
                subcontrol-position: top left;
                left: 12px;
                top: 4px;
                padding: 2px 8px;
                color: {ACCENT_COLOR};
                font-size: 10pt;
                font-weight: bold;
            }}

            /* ═══════════════════════════════════════════════════════════════
               PROGRESS BAR (QProgressBar)
               ═══════════════════════════════════════════════════════════════ */
            QProgressBar {{
                background-color: #1a1a1a;
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                text-align: center;
                color: {TEXT_PRIMARY};
                font-weight: bold;
                min-height: 20px;
            }}
            
            QProgressBar::chunk {{
                background: qlineargradient(x1:0, y1:0, x2:1, y2:0,
                    stop:0 {ACCENT_COLOR}, stop:1 #00bfa5);
                border-radius: 3px;
            }}

            /* ═══════════════════════════════════════════════════════════════
               SCROLLBARS (Minimal VS Code Style)
               ═══════════════════════════════════════════════════════════════ */
            QScrollBar:vertical {{
                background-color: transparent;
                width: 10px;
                margin: 0;
            }}
            
            QScrollBar::handle:vertical {{
                background-color: #4a4a4a;
                border-radius: 5px;
                min-height: 30px;
                margin: 2px;
            }}
            
            QScrollBar::handle:vertical:hover {{
                background-color: #5a5a5a;
            }}
            
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
                height: 0;
                background: none;
            }}
            
            QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {{
                background: none;
            }}
            
            QScrollBar:horizontal {{
                background-color: transparent;
                height: 10px;
                margin: 0;
            }}
            
            QScrollBar::handle:horizontal {{
                background-color: #4a4a4a;
                border-radius: 5px;
                min-width: 30px;
                margin: 2px;
            }}
            
            QScrollBar::handle:horizontal:hover {{
                background-color: #5a5a5a;
            }}
            
            QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {{
                width: 0;
                background: none;
            }}
            
            QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal {{
                background: none;
            }}

            /* ═══════════════════════════════════════════════════════════════
               LABELS & FORMS
               ═══════════════════════════════════════════════════════════════ */
            QLabel {{
                color: {TEXT_PRIMARY};
                background-color: transparent;
            }}
            
            QLabel#titleLabel {{
                font-size: 18pt;
                font-weight: bold;
                color: {TEXT_PRIMARY};
                padding: 10px 0;
            }}
            
            QLabel#subtitleLabel {{
                font-size: 12pt;
                font-weight: bold;
                color: {TEXT_SECONDARY};
            }}
            
            QFormLayout {{
                spacing: 12px;
            }}

            /* ═══════════════════════════════════════════════════════════════
               CHECKBOXES & RADIO BUTTONS
               ═══════════════════════════════════════════════════════════════ */
            QCheckBox {{
                spacing: 8px;
                color: {TEXT_PRIMARY};
            }}
            
            QCheckBox::indicator {{
                width: 18px;
                height: 18px;
                border: 2px solid {BORDER_DEFAULT};
                border-radius: 3px;
                background-color: {BG_INPUT};
            }}
            
            QCheckBox::indicator:checked {{
                background-color: {ACCENT_COLOR};
                border-color: {ACCENT_COLOR};
            }}
            
            QCheckBox::indicator:hover {{
                border-color: {ACCENT_COLOR};
            }}
            
            QRadioButton {{
                spacing: 8px;
                color: {TEXT_PRIMARY};
            }}
            
            QRadioButton::indicator {{
                width: 18px;
                height: 18px;
                border: 2px solid {BORDER_DEFAULT};
                border-radius: 10px;
                background-color: {BG_INPUT};
            }}
            
            QRadioButton::indicator:checked {{
                background-color: {BG_INPUT};
                border-color: {ACCENT_COLOR};
            }}
            
            QRadioButton::indicator:checked::after {{
                background-color: {ACCENT_COLOR};
            }}

            /* ═══════════════════════════════════════════════════════════════
               SLIDERS
               ═══════════════════════════════════════════════════════════════ */
            QSlider::groove:horizontal {{
                background-color: #1a1a1a;
                border: 1px solid {BORDER_DEFAULT};
                height: 6px;
                border-radius: 3px;
            }}
            
            QSlider::handle:horizontal {{
                background-color: {ACCENT_COLOR};
                border: none;
                width: 16px;
                height: 16px;
                margin: -5px 0;
                border-radius: 8px;
            }}
            
            QSlider::handle:horizontal:hover {{
                background-color: {ACCENT_HOVER};
            }}
            
            QSlider::sub-page:horizontal {{
                background-color: {ACCENT_COLOR};
                border-radius: 3px;
            }}

            /* ═══════════════════════════════════════════════════════════════
               MENUS & MENU BAR
               ═══════════════════════════════════════════════════════════════ */
            QMenuBar {{
                background-color: {BG_SURFACE};
                color: {TEXT_PRIMARY};
                border-bottom: 1px solid {BORDER_DEFAULT};
                padding: 4px;
            }}
            
            QMenuBar::item {{
                background-color: transparent;
                padding: 6px 12px;
                border-radius: 4px;
            }}
            
            QMenuBar::item:selected {{
                background-color: {BG_HOVER};
            }}
            
            QMenu {{
                background-color: {BG_SURFACE};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 6px;
                padding: 6px;
            }}
            
            QMenu::item {{
                padding: 8px 24px;
                border-radius: 4px;
            }}
            
            QMenu::item:selected {{
                background-color: {ACCENT_COLOR};
                color: white;
            }}
            
            QMenu::separator {{
                height: 1px;
                background-color: {BORDER_DEFAULT};
                margin: 6px 12px;
            }}

            /* ═══════════════════════════════════════════════════════════════
               STATUS BAR
               ═══════════════════════════════════════════════════════════════ */
            QStatusBar {{
                background-color: {BG_SURFACE};
                color: {TEXT_SECONDARY};
                border-top: 1px solid {BORDER_DEFAULT};
                padding: 4px 12px;
                font-size: 9pt;
            }}
            
            QStatusBar::item {{
                border: none;
            }}

            /* ═══════════════════════════════════════════════════════════════
               SCROLL AREA
               ═══════════════════════════════════════════════════════════════ */
            QScrollArea {{
                background-color: {BG_WINDOW};
                border: none;
            }}
            
            QScrollArea > QWidget > QWidget {{
                background-color: {BG_WINDOW};
            }}

            /* ═══════════════════════════════════════════════════════════════
               MESSAGE BOXES & DIALOGS
               ═══════════════════════════════════════════════════════════════ */
            QMessageBox {{
                background-color: {BG_SURFACE};
            }}
            
            QMessageBox QLabel {{
                color: {TEXT_PRIMARY};
                font-size: 10pt;
            }}
            
            QFileDialog {{
                background-color: {BG_WINDOW};
            }}

            /* ═══════════════════════════════════════════════════════════════
               TOOL TIPS
               ═══════════════════════════════════════════════════════════════ */
            QToolTip {{
                background-color: {BG_SURFACE};
                color: {TEXT_PRIMARY};
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
                padding: 6px 10px;
                font-size: 9pt;
            }}

            /* ═══════════════════════════════════════════════════════════════
               WEB ENGINE VIEW (for Plotly charts)
               ═══════════════════════════════════════════════════════════════ */
            QWebEngineView {{
                background-color: #1a1a1a;
                border: 1px solid {BORDER_DEFAULT};
                border-radius: 4px;
            }}
        """)


def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    window = RINAnalyzerGUI()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()