import os
import re
from enum import Enum
from typing import Optional
import google.generativeai as genai
from huggingface_hub import InferenceClient
from src.utils.config import SecureConfig

class LLMProvider(str, Enum):
    GEMINI = "gemini"
    HUGGING_FACE = "huggingface"

def format_math_prompt(question: str) -> str:
    """Format math problems according to model recommendations"""
    return f"""Please reason step by step, and put your final answer within \\boxed{{}}.

Question: {question}
Answer:"""

def extract_boxed_answer(text: str) -> str:
    """Extract LaTeX boxed answers from model response"""
    match = re.search(r'\\boxed{([^}]+)}', text)
    return match.group(1) if match else text

class LLMOrchestrator:
    def __init__(self):
        self.client = None
        self._configure_providers()

    def _configure_providers(self):
        self.active_provider = SecureConfig.get('LLM_PROVIDER', LLMProvider.GEMINI)

        if self.active_provider == LLMProvider.GEMINI:
            genai.configure(api_key=SecureConfig.get('GEMINI_API_KEY'))
            self.client = genai.GenerativeModel('gemini-pro')
        elif self.active_provider == LLMProvider.HUGGING_FACE:
            self.client = InferenceClient(
                token=SecureConfig.get('HUGGING_FACE_API_KEY'),
                model="deepseek-ai/DeepSeek-R1-Distill-Qwen-32B"
            )

    def generate(self, prompt: str) -> str:
        if self.active_provider == LLMProvider.GEMINI:
            return self._gemini_generate(prompt)
        return self._hf_generate(prompt)

    def _gemini_generate(self, prompt: str) -> str:
        try:
            config = {'generation_config': {'include_thoughts': True}} # Enable thinking process
            response = self.client.models.generate_content(
                model='gemini-2.0-flash-thinking-exp', # Use Flash Thinking model
                contents=prompt,
                config=config
            )
            full_response_text = "" # Capture both thoughts and response
            for part in response.candidates[0].content.parts:
                if part.thought:
                    full_response_text += f"**Model Thought:**\n{part.text}\n\n" # Mark thoughts clearly
                else:
                    full_response_text += f"**Model Response:**\n{part.text}\n\n" # Mark response

            return full_response_text.strip() # Return combined text

        except Exception as e:
            raise RuntimeError(f"Gemini error: {str(e)}")

    def _hf_generate(self, prompt: str) -> str:
        try:
            return self.client.text_generation(
                prompt,
                max_new_tokens=2048,
                temperature=0.6,
                top_p=0.95,
                repetition_penalty=1.2,
                do_sample=True,
                seed=42,
                stop_sequences=["</s>"],
                return_full_text=False
            )
        except Exception as e:
            raise RuntimeError(f"Hugging Face error: {str(e)}")
