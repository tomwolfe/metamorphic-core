# Use a single stage for simplicity and standard system-wide installs
FROM python:3.11-slim

WORKDIR /app
ENV PYTHONPATH=/app:/app/src

# System dependencies needed for some Python packages (like build-essential) and runtime
# build-essential is needed for some packages to compile native extensions
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    netcat-openbsd \
    build-essential \
    # Add git as it might be needed by some pip packages or spaCy downloads
    git \
    && rm -rf /var/lib/apt/lists/*

# Install dependencies system-wide (removed --user)
# Ensure pip is upgraded before installing requirements
COPY requirements/base.txt requirements/dev.txt ./
RUN pip install --no-cache-dir --upgrade pip && \
    pip install --no-cache-dir -r base.txt -r dev.txt

# Download and install spaCy model system-wide
# This command installs the model data and links it into the system site-packages
# This step MUST come AFTER spacy is installed via pip
RUN python -m spacy download en_core_web_sm

# Clean up build dependencies if they are not needed at runtime to reduce image size
# build-essential and git are often only needed during pip install/spacy download
RUN apt-get purge -y build-essential git && apt-get autoremove -y && rm -rf /var/lib/apt/lists/*

# Application code
COPY . .

# The default PATH environment variable in this base image already includes
# /usr/local/bin and /usr/local/sbin, where executables from system-wide
# pip installs are placed. The /root/.local/bin path is no longer relevant
# as we are not using --user installs.
# Remove the original line: ENV PATH="/root/.local/bin:${PATH}"

# Command to run the application is specified in docker-compose.yml
# CMD ["python", "src/api/server.py"] # Not needed here as docker-compose overrides it