# tests/test_cli.py

import pytest
import argparse
import os
import sys
from unittest.mock import patch
from src.cli.main import cli_entry_point

class TestCLIArguments:

    def test_cli_default_args(self):
        with patch('sys.argv', ['main.py']), \
             patch('os.path.exists', return_value=True), \
             patch('os.path.isdir', return_value=True):
            try:
                cli_entry_point()
            except SystemExit as e:
                pytest.fail(f"cli_entry_point() raised SystemExit unexpectedly: {e}")

    def test_cli_custom_args_exist(self):
        with patch('sys.argv', ['main.py', '--roadmap', 'custom_roadmap.json', '--output-dir', 'custom_output']), \
             patch('os.path.exists', return_value=True), \
             patch('os.path.isdir', return_value=True):
            try:
                cli_entry_point()
            except SystemExit as e:
                pytest.fail(f"cli_entry_point() raised SystemExit unexpectedly: {e}")

    def test_cli_roadmap_not_exist(self):
        with patch('sys.argv', ['main.py', '--roadmap', 'nonexistent.json']), \
             patch('os.path.exists', return_value=False), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()

    def test_cli_output_dir_not_exist(self):
        with patch('sys.argv', ['main.py', '--output-dir', 'nonexistent_dir']), \
             patch('os.path.exists', return_value=False), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()

    def test_cli_output_dir_is_file(self):
        with patch('sys.argv', ['main.py', '--output-dir', 'output_is_file']), \
             patch('os.path.exists', return_value=True), \
             patch('os.path.isdir', return_value=False), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()

    def test_cli_help_message(self, capsys):
        with patch('sys.argv', ['main.py', '--help']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "usage:" in captured.out
        assert "--roadmap" in captured.out
        assert "--output-dir" in captured.out

    def test_cli_version_message(self, capsys):
        with patch('sys.argv', ['main.py', '--version']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "Metamorphic CLI v0.1.0-alpha" in captured.out