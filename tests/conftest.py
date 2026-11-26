"""Skip tests whose optional requirements are missing, instead of failing them.

* Tests named ``test_cpp_*`` or marked ``native`` exercise the native C++17
  accelerators and need a compiler (``$CXX``, ``g++`` or ``clang++``).
* Tests marked ``audit`` compare against the independent CVXPY/Clarabel
  reference solvers (``pip install "dagcert[audit]"``).
"""
from __future__ import annotations

import importlib.util
import os
import shutil

import pytest

HAS_CXX = bool(os.environ.get("CXX") or shutil.which("g++") or shutil.which("clang++"))
HAS_CVXPY = importlib.util.find_spec("cvxpy") is not None


def pytest_collection_modifyitems(config, items):
    no_cxx = pytest.mark.skip(reason="needs a C++17 compiler ($CXX, g++ or clang++)")
    no_cvxpy = pytest.mark.skip(reason='needs CVXPY: pip install "dagcert[audit]"')
    for item in items:
        if item.name.startswith("test_cpp"):
            item.add_marker(pytest.mark.native)
        if item.get_closest_marker("native") and not HAS_CXX:
            item.add_marker(no_cxx)
        if item.get_closest_marker("audit") and not HAS_CVXPY:
            item.add_marker(no_cvxpy)
