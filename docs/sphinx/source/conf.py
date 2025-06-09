import os
import sys

sys.path.insert(0, os.path.abspath("../../src"))

project = "exov6"
extensions = ["breathe", "myst_parser"]

# Treat common compiler attributes as id/paren attributes so the
# C++ domain parses generated declarations correctly.
cpp_id_attributes = ["__vector", "__attribute__"]
cpp_paren_attributes = ["__attribute__"]

breathe_projects = {"exov6": os.path.abspath("../../build/xml")}
breathe_default_project = "exov6"

html_theme = "sphinx_rtd_theme"

templates_path = ["_templates"]
exclude_patterns = []

html_static_path = ["_static"]
