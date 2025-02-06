from flask import Flask, request, jsonify
import logging, redis
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from src.core.llm_orchestration import LLMOrchestrator # Correct import
from src.utils.config import SecureConfig
import os # ADD THIS LINE

startup_done = False # Flag to track if startup has run

app = Flask(__name__)
limiter = Limiter(get_remote_address, app=app)  # Initialize the limiter

logging.basicConfig(level=logging.INFO) # Set logging level

# Initialize LLM Orchestrator
llm_orchestrator = LLMOrchestrator()
app.llm_orchestrator = llm_orchestrator # Make it accessible in app context

@app.route('/generate', methods=['POST'])
@limiter.limit("5/minute")
def generate_endpoint():
    # Extract input from the request
    data = request.get_json()
    if not data or 'prompt' not in data:
        return jsonify({"error": "Missing prompt"}), 400

    try:
        # Use LLM Orchestrator to generate a response
        response = app.llm_orchestrator.generate(data['prompt']) # Use orchestrator
        return jsonify({
            "response": response, # Return text response
            "status": "success"
        }), 200

    except Exception as e:
        return jsonify({
            "error": str(e),
            "status": "error"
        }), 500

@app.route('/health')
def health_check():
    """Health check endpoint."""
    return jsonify({"status": "ready"}), 200

@app.before_request
def startup_debug():
    global startup_done
    if not startup_done:
        import socket
        hostname = socket.gethostname()
        ip = socket.gethostbyname(hostname)
        app.logger.info(f"Flask running on {ip}:5000")
        app.logger.info(f"Flask host binding to: 0.0.0.0:5000") # Explicit log
        try:
            redis_client = redis.Redis(host='localhost', port=6379)
            response = redis_client.ping()
            if response:
                app.logger.info("Redis connection successful")
            else:
                app.logger.warning("Redis ping failed but connection might still be alive.")
            app.logger.info("Placeholder: Successfully checked Redis connection (if configured)")
        except Exception as e:
            app.logger.error(f"Placeholder: Redis connection check failed (if configured): {str(e)}")

        # --- ADD THIS SECTION: Log environment variables ---
        app.logger.info("--- Environment Variables ---")
        keys_to_log = ['LLM_PROVIDER', 'GEMINI_API_KEY', 'YOUR_GITHUB_API_KEY', 'HUGGING_FACE_API_KEY', 'ZAP_API_KEY']
        for key in keys_to_log:
            value = os.environ.get(key, 'NOT SET')
            app.logger.info(f"{key}: {value}")
        app.logger.info("--- End Environment Variables ---")
        # --- END ADDED SECTION ---
        startup_done = True


if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
