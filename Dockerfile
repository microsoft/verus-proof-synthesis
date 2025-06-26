# Use Ubuntu as base image for better compatibility with both Python and Rust
FROM ubuntu:22.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV PYTHONDONTWRITEBYTECODE=1
ENV PYTHONUNBUFFERED=1
ENV RUST_BACKTRACE=1

# Install system dependencies
RUN apt-get update && apt-get install -y \
    # Python dependencies
    python3.10 \
    python3.10-dev \
    python3-pip \
    python3.10-venv \
    # Rust dependencies
    curl \
    build-essential \
    pkg-config \
    libssl-dev \
    # Git for fetching dependencies
    git \
    vim \
    unzip \
    # System utilities
    sudo \
    # Azure CLI for authentication (optional)
    ca-certificates \
    gnupg \
    lsb-release \
    # Clean up
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Create a non-root user for security
RUN useradd -m -s /bin/bash appuser
RUN adduser appuser sudo
# Allow sudo without password for convenience (optional - remove for production)
RUN echo "appuser ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers
USER appuser

# Install Rust
WORKDIR /home/appuser
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/home/appuser/.cargo/bin:${PATH}" 

# Install Azure CLI
RUN curl -sL https://aka.ms/InstallAzureCLIDeb | sudo bash

# Clone and build Verus
WORKDIR /home/appuser
RUN git clone https://github.com/verus-lang/verus.git
WORKDIR /home/appuser/verus
RUN git checkout 33269ac6a0ea33a08109eefe5016c1fdd0ce9fbd

# Build Verus (following the proper Verus build process)
WORKDIR /home/appuser/verus/source
RUN bash -c "source /home/appuser/.cargo/env && source ../tools/activate && ./tools/get-z3.sh && vargo build --release"
RUN cargo install verusfmt

# Set working directory back to app
WORKDIR /home/appuser
RUN git clone https://github.com/microsoft/verus-proof-synthesis.git

WORKDIR /home/appuser/verus-proof-synthesis
# Create virtual environment and install Python dependencies
RUN python3.10 -m venv /home/appuser/venv
RUN git checkout artifact
ENV PATH="/home/appuser/venv/bin:/home/appuser/verus/source/target-verus/release:$PATH"
RUN pip install --upgrade pip setuptools wheel
RUN pip install -r requirements.txt

# You can override this when running the container
CMD ["/bin/bash"]

# Add labels for metadata
LABEL maintainer="verus-proof-synthesis"
LABEL description="Docker image for Verus proof synthesis project"
LABEL version="0.1.0" 