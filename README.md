# RIN Analyzer: Residue Interaction Network Analysis Tool

![RIN Analyzer GUI](docs/assets/gui_screenshot.png)

## Overview

**RIN Analyzer** is a comprehensive bioinformatics tool developed to identify **allosteric** and **orthosteric** binding sites in proteins using Residue Interaction Networks (RINs). 

Unlike traditional methods that rely solely on geometric pocket detection, RIN Analyzer integrates **network centrality metrics** (Betweenness, Closeness, Degree) with geometric analysis to detect "cryptic" pockets and functional hubs.

This project was developed as part of a Master's Thesis and validated against the **AlloBench dataset** (100 proteins), demonstrating high sensitivity in detecting novel binding sites without prior ligand knowledge.

## Key Features

* **🔍 Discovery Mode:** Identifies potential binding sites (pockets) without requiring a reference ligand.
* **🕸️ Network Analysis:** Calculates residue centrality to find communication hubs within the protein structure.
* **⚡ Consensus Scoring:** Uses a hybrid scoring algorithm combining geometric volume, druggability, and network centrality.
* **📊 Benchmarking:** Includes a built-in validation engine compatible with AlloBench datasets.
* **🧪 PyMOL Integration:** Generates `.pml` scripts for publication-ready 3D visualization.
* **📈 Interactive Plots:** Built-in Plotly graphs for centrality and residue analysis.

## Validation & Performance

The tool has been benchmarked using the AlloBench dataset (n=100 proteins). Key performance metrics include:

| Metric | Score (Core) | Description |
| :--- | :--- | :--- |
| **Sensitivity** | High | Successfully identifies known allosteric sites. |
| **Discovery Rate** | >60% | Detects novel pockets in "Discovery Mode". |
| **Speed** | < 10s | Average processing time per protein structure. |

*(Detailed validation tables can be found in the `data/results` directory.)*

## Installation

### Prerequisites
* Python 3.8+
* pip

### Setup
1.  Clone the repository:
    ```bash
    git clone [https://github.com/YOUR_USERNAME/RIN-Analyzer.git](https://github.com/YOUR_USERNAME/RIN-Analyzer.git)
    cd RIN-Analyzer
    ```

2.  Install dependencies:
    ```bash
    pip install -r requirements.txt
    ```

## Usage

1.  Run the application via terminal:
    ```bash
    python src/RINAnalyzer.py
    ```
2.  **Load PDB:** Click "Load PDB File" to select a protein structure.
3.  **Analyze:** Click "Run Analysis" to calculate RINs and detect pockets.
4.  **Visualize:** Use the "PyMOL" tab to export visualization scripts.

## Project Structure

```text
src/          # Source code for the GUI and Logic
data/         # Benchmark datasets (AlloBench) and results
docs/         # Thesis report and user documentation

Technologies Used
GUI: PyQt6

Bioinformatics: BioPython

Network Analysis: NetworkX

Visualization: Plotly, PyMOL (Scripting)

Data Processing: Pandas, NumPy, Scikit-learn

License
This project is licensed under the MIT License - see the LICENSE file for details.