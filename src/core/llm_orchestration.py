import os
import re
from enum import Enum
from typing import Optional
from google import genai
from huggingface_hub import InferenceClient
from src.utils.config import SecureConfig
from pydantic import BaseModel, ValidationError

class LLMProvider(str, Enum):
    GEMINI = "gemini"
    HUGGING_FACE = "huggingface"

class LLMConfig(BaseModel):
    provider: LLMProvider
    gemini_api_key: Optional[str] = None
    hf_api_key: Optional[str] = None
    max_retries: int = 3
    timeout: int = 30

class LLMOrchestrator:
    def __init__(self):
        self.client = None
        self.active_provider = None
        self.config = self._load_config()
        self._configure_providers()

    def _load_config(self) -> LLMConfig:
        try:
            return LLMConfig(
                provider=LLMProvider(SecureConfig.get('LLM_PROVIDER', LLMProvider.GEMINI)),
                gemini_api_key=SecureConfig.get('GEMINI_API_KEY'),
                hf_api_key=SecureConfig.get('HUGGING_FACE_API_KEY'),
                max_retries=int(SecureConfig.get('LLM_MAX_RETRIES', 3)),
                timeout=int(SecureConfig.get('LLM_TIMEOUT', 30))
            )
        except ValidationError as e:
            raise RuntimeError(f"Invalid LLM configuration: {str(e)}")

    def _configure_providers(self):
        if self.config.provider == LLMProvider.GEMINI:
            if not self.config.gemini_api_key:
                raise RuntimeError("GEMINI_API_KEY is required for Gemini provider")
            genai.configure(api_key=self.config.gemini_api_key)
            self.client = genai.GenerativeModel('gemini-pro')

        elif self.config.provider == LLMProvider.HUGGING_FACE:
            if not self.config.hf_api_key:
                raise RuntimeError("HUGGING_FACE_API_KEY is required for Hugging Face provider")
            self.client = InferenceClient(
                token=self.config.hf_api_key,
                model="deepseek-ai/DeepSeek-R1-Distill-Qwen-32B"
            )

        else:
            raise ValueError(f"Unsupported LLM provider: {self.config.provider}")

    def generate(self, prompt: str) -> str:
        for attempt in range(self.config.max_retries):
            try:
                if self.config.provider == LLMProvider.GEMINI:
                    return self._gemini_generate(prompt)
                return self._hf_generate(prompt)
            except Exception as e:
                if attempt == self.config.max_retries - 1:
                    raise RuntimeError(f"LLM API failed after {self.config.max_retries} attempts: {str(e)}")

    def _gemini_generate(self, prompt: str) -> str:
        try:
            response = self.client.generate_content(prompt)
            return ''.join(part.text for part in response.candidates[0].content.parts)
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
                stop_sequences=["</s>"], # Line 85 - Corrected: Closing quote added
                return_full_text=False
            )
        except Exception as e:
            raise RuntimeError(f"Hugging Face error: {str(e)}")

def format_math_prompt(question: str) -> str:
    return f"""Please reason step by step and put your final answer within \\boxed{{}}.

Question: {question}
Answer:"""

def extract_boxed_answer(text: str) -> str:
    match = re.search(r'\\boxed{([^}]+)}', text)
    return match.group(1) if match else text
