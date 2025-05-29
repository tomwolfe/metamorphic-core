# Use a multi-stage build for smaller final image size

# --- Stage 1: Builder ---
# This stage installs all build-time dependencies and Python packages
FROM python:3.11-slim as builder

WORKDIR /app

# Install system dependencies needed for building Python packages (e.g., psycopg2, numpy)
# and for cloning repos (git)
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    git \
    # Add any other build-time only dependencies here
    && rm -rf /var/lib/apt/lists/*

# Copy and install Python dependencies
# Ensure pip is upgraded before installing requirements
COPY requirements/base.txt requirements/dev.txt ./
RUN pip install --no-cache-dir --upgrade pip && \
    pip install --no-cache-dir -r base.txt -r dev.txt

# Download and install spaCy model
# This command installs the model data and links it into the system site-packages
# This step MUST come AFTER spacy is installed via pip
RUN python -m spacy download en_core_web_sm


# --- Stage 2: Runtime ---
# This stage contains only the necessary runtime dependencies and application code
FROM python:3.11-slim

WORKDIR /app
ENV PYTHONPATH=/app:/app/src

# Install only runtime system dependencies
# curl and netcat-openbsd are needed for health checks and network operations
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    netcat-openbsd \
    # Add any other runtime only dependencies here
    && rm -rf /var/lib/apt/lists/*

# Copy installed Python packages from the builder stage
# This copies the entire site-packages directory, including spaCy models
COPY --from=builder /usr/local/lib/python3.11/site-packages /usr/local/lib/python3.11/site-packages

# Copy application code
# Ensure .dockerignore is configured to exclude unnecessary files
COPY . .

# The default PATH environment variable in this base image already includes
# /usr/local/bin and /usr/local/sbin, where executables from system-wide
# pip installs are placed.

# Command to run the application is specified in docker-compose.yml