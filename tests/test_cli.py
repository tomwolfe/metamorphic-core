# tests/test_cli.py
import pytest
import argparse
import os
import sys
from unittest.mock import patch
from src.cli.main import cli_entry_point

class TestCLIArguments:
    """Test suite for CLI argument parsing and validation."""

    def test_cli_help_message(self, capsys):
        """Test --help flag displays usage information."""
        with patch('sys.argv', ['main.py', '--help']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "usage:" in captured.out
        assert "--roadmap" in captured.out
        assert "--output-dir" in captured.out

    def test_cli_version_message(self, capsys):
        """Test --version flag displays correct version string."""
        with patch('sys.argv', ['main.py', '--version']), \
             pytest.raises(SystemExit) as excinfo:
            cli_entry_point()
        captured = capsys.readouterr()
        assert "Metamorphic CLI v0.1.0-alpha" in captured.out

    def test_cli_default_args(self, capsys):
        """Test CLI with default arguments."""
        with patch('sys.argv', ['main.py']), \
             patch('src.cli.main._validate_roadmap_path', return_value='ROADMAP.json'), \
             patch('src.cli.main._validate_output_dir', return_value='./output'):
            cli_entry_point()
            captured = capsys.readouterr()
            assert "ROADMAP.json" in captured.out
            assert "./output" in captured.out

    def test_cli_custom_args_exist(self, capsys):
        """Test CLI with custom valid arguments."""
        with patch('sys.argv', ['main.py', '--roadmap', 'custom_roadmap.json', '--output-dir', 'custom_output']), \
             patch('src.cli.main._validate_roadmap_path', return_value='custom_roadmap.json'), \
             patch('src.cli.main._validate_output_dir', return_value='custom_output'):
            cli_entry_point()
            captured = capsys.readouterr()
            assert "custom_roadmap.json" in captured.out
            assert "custom_output" in captured.out

    def test_cli_roadmap_not_exist(self):
        """Test CLI with non-existent roadmap file."""
        with patch('sys.argv', ['main.py', '--roadmap', 'nonexistent.json']), \
             patch('src.cli.main._validate_roadmap_path', side_effect=argparse.ArgumentTypeError("File does not exist")), \
             pytest.raises(SystemExit):
            cli_entry_point()

    def test_cli_output_dir_not_exist(self):
        """Test CLI with non-existent output directory."""
        with patch('sys.argv', ['main.py', '--output-dir', 'nonexistent_dir']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Directory does not exist")), \
             pytest.raises(SystemExit):
            cli_entry_point()

    def test_cli_output_dir_is_file(self):
        """Test CLI when output directory path is actually a file."""
        with patch('sys.argv', ['main.py', '--output-dir', 'output_is_file']), \
             patch('src.cli.main._validate_output_dir', side_effect=argparse.ArgumentTypeError("Path is not a directory")), \
             pytest.raises(SystemExit):
            cli_entry_point()