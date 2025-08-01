# Copyright (c) Microsoft Corporation. #
# Licensed under the MIT license.      #
import openai
from openai import AzureOpenAI, OpenAI
from azure.identity import (
    ChainedTokenCredential,
    AzureCliCredential,
    ManagedIdentityCredential,
    get_bearer_token_provider,
)
import time
import random


def is_reasoning_model(model_name):
    """
    Check if the given model name is a reasoning model (o1, o3, o4 series).

    Args:
        model_name (str): The name of the model to check

    Returns:
        bool: True if the model is a reasoning model, False otherwise
    """
    if not model_name:
        return False

    model_name_lower = model_name.lower()
    reasoning_model_prefixes = ["o1", "o3", "o4"]

    # Check if the model name starts with any reasoning model prefix
    # This is more precise than just checking if the string contains these patterns
    for prefix in reasoning_model_prefixes:
        if model_name_lower.startswith(prefix):
            return True

    return False


class LLM:
    def __init__(self, config, logger):
        self.config = config
        self.logger = logger
        self.client = []
        # there may be no key and instead authentication is used
        if config.use_openai:
            if len(config.aoai_api_key) == 0:
                self.logger.info("Using OpenAI API Key from environment variable")
                self.client.append(
                    OpenAI(
                        api_key=os.getenv("OPENAI_API_KEY"),
                        base_url=config.aoai_api_base[0],
                        max_retries=config.aoai_max_retries,
                    )
                )
            else:
                for i in range(len(config.aoai_api_key)):
                    self.client.append(
                        OpenAI(
                            api_key=config.aoai_api_key[i],
                            base_url=config.aoai_api_base[i],
                            max_retries=config.aoai_max_retries,
                        )
                    )
        # there may be no key and instead authentication is used
        elif len(config.aoai_api_key) == 0:
            scope = "https://cognitiveservices.azure.com/.default"

            credential = get_bearer_token_provider(
                ChainedTokenCredential(
                    AzureCliCredential(),
                    ManagedIdentityCredential(),
                ),
                scope,
            )

            self.client.append(
                AzureOpenAI(
                    azure_ad_token_provider=credential,
                    azure_endpoint=config.aoai_api_base[0],
                    api_version=config.aoai_api_version,
                    max_retries=config.aoai_max_retries,
                )
            )
        else:
            for i in range(len(config.aoai_api_key)):
                self.client.append(
                    AzureOpenAI(
                        api_key=config.aoai_api_key[i],
                        azure_endpoint=config.aoai_api_base[i],
                        api_version=config.aoai_api_version,
                        max_retries=config.aoai_max_retries,
                    )
                )
        self.client_id = random.randint(0, len(self.client) - 1)

    def _add_client_id(self):
        self.client_id += 1
        self.client_id %= len(self.client)

    def _reset_client_id(self):
        if len(self.client) == 1:
            return
        self.client_id += random.randint(1, len(self.client) - 1)
        self.client_id %= len(self.client)

    def infer_llm(
        self,
        engine,
        instruction,
        exemplars,
        query,
        system_info=None,
        answer_num=1,
        max_tokens=2048,
        temp=0.7,
        json=False,
        return_msg=False,
        verbose=False,
        timeout=100,
    ):
        """
        Args:
            engine: str - Model engine name
            instruction: str - Initial instruction for the assistant
            exemplars: list of dict {"query": str, "answer": str} - Few-shot examples
            query: str - The actual query to process
            system_info: str - System message content
            answer_num: int - Number of completions to generate
            max_tokens: int - Maximum tokens in response
            temp: float - Temperature for sampling
            json: bool - Whether to request JSON format response
            return_msg: bool - Whether to return messages along with responses
            verbose: bool - Whether to log verbose information
            timeout: int - Timeout for API calls in seconds
        Returns:
            answers: list of str (or tuple of (list of str, messages) if return_msg=True)
        """
        self._reset_client_id()
        if verbose:
            self.logger.info(f"Using client {self.client_id}")

        system_info = (
            "You are a helpful AI assistant." if system_info is None else system_info
        )
        messages = [{"role": "system", "content": system_info}]

        if instruction is not None:
            messages.append({"role": "user", "content": instruction})
            messages.append({"role": "assistant", "content": "OK, I'm ready to help."})

        if exemplars is not None:
            for exemplar in exemplars:
                messages.append({"role": "user", "content": exemplar["query"]})
                messages.append({"role": "assistant", "content": exemplar["answer"]})

        messages.append({"role": "user", "content": query})

        tries = 0
        max_tries = 5

        while tries <= max_tries:
            try:
                self.logger.info(
                    f"Invoking model {engine} with client {self.client_id} with num={answer_num}"
                )
                if is_reasoning_model(engine):
                    answers = self.client[self.client_id].chat.completions.create(
                        model=engine,
                        messages=messages,
                        temperature=temp,
                        max_completion_tokens=20000,
                        n=answer_num,
                    )
                else:
                    answers = self.client[self.client_id].chat.completions.create(
                        model=engine,
                        messages=messages,
                        temperature=temp,
                        max_tokens=max_tokens,
                        n=answer_num,
                        response_format={"type": "json_object" if json else "text"},
                        timeout=timeout,
                    )
                break
            except openai.APITimeoutError as e:
                self.logger.warning(f"API Timeout Error: {str(e)}")
                time.sleep(10)
                tries += 1
                continue
            except openai.NotFoundError as e:
                self.logger.warning(
                    f"Model not found error: {str(e)}. Switching client."
                )
                self._add_client_id()
                continue
            except openai.BadRequestError as e:
                self.logger.error(f"Bad request error: {str(e)}")
                if return_msg:
                    return [], messages
                else:
                    return []
            except openai.RateLimitError as e:
                if len(self.client) == 1:
                    self.logger.warning(
                        f"Rate limit error: {str(e)}. Waiting 10 seconds."
                    )
                    time.sleep(10)
                else:
                    self.logger.warning(
                        f"Rate limit error: {str(e)}. Switching client."
                    )
                    self._add_client_id()
                tries += 1
                continue
            except openai.InternalServerError as e:
                tries += 1
                if tries > max_tries:
                    self.logger.error(
                        f"Internal Server Error after {tries} tries: {str(e)}"
                    )
                    if return_msg:
                        return [], messages
                    else:
                        return []
                self.logger.warning(
                    f"Internal Server Error (attempt {tries}): {str(e)}. Retrying..."
                )
                time.sleep(10)
                continue
            except Exception as e:
                self.logger.error(f"Unexpected error during API call: {str(e)}")
                if return_msg:
                    return [], messages
                else:
                    return []

        # Log the input and output tokens here
        self.logger.info(f"Input tokens: {answers.usage.prompt_tokens}")
        self.logger.info(f"Output tokens: {answers.usage.completion_tokens}")

        if return_msg:
            return [response.message.content for response in answers.choices], messages
        else:
            return [response.message.content for response in answers.choices]

    def infer_llm_with_history(
        self,
        engine,
        history,
        query,
        answer_num=1,
        max_tokens=2048,
        temp=0.7,
        json=False,
        return_msg=False,
        verbose=False,
    ):
        """
        Args:
            instruction: str
            history: List
            query: str
        Returns:
            answers: list of str
        """
        self._reset_client_id()
        # self.client_id = 0
        if verbose:
            self.logger.info(f"Using client {self.client_id}")

        messages = history[:]
        messages.append({"role": "user", "content": query})

        while True:
            try:
                answers = self.client[self.client_id].chat.completions.create(
                    model=engine,
                    messages=messages,
                    temperature=temp,
                    max_tokens=max_tokens,
                    top_p=1.0,
                    n=answer_num,
                    frequency_penalty=0,
                    presence_penalty=0,
                    stop=None,
                    response_format={"type": "json_object" if json else "text"},
                )
                break
            except openai.NotFoundError:
                self._add_client_id()
                continue
            except openai.BadRequestError:
                if return_msg:
                    return [], messages
                else:
                    return []
            except openai.RateLimitError:
                if len(self.client) == 1:
                    time.sleep(10)
                else:
                    self._add_client_id()
                continue
        if return_msg:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ], messages
        else:
            return [
                response.message.content if response.finish_reason != "length" else ""
                for response in answers.choices
            ]
