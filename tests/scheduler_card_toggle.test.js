import { describe, it, expect, vi, beforeAll, afterEach } from 'vitest';

beforeAll(async () => {
  await import('../custom_components/foxess/scheduler_card.js');
});

afterEach(() => {
  document.body.innerHTML = '';
});

const DEVICE_SN = 'SN123456';

function makeHass(schedulerState, sendMessagePromise) {
  return {
    states: {
      'sensor.foxess_scheduler_enabled': {
        state: schedulerState,
        attributes: { friendly_name: 'FoxESS Scheduler Enabled' },
      },
      'sensor.foxess_scheduler_groups': {
        state: '0',
        attributes: { groups: [], device_sn: DEVICE_SN },
      },
    },
    connection: {
      sendMessagePromise: sendMessagePromise ?? vi.fn().mockResolvedValue({ ok: true }),
    },
  };
}

function mountCard(hass) {
  const Card = customElements.get('foxess-scheduler-card');
  const card = new Card();
  document.body.appendChild(card);
  card.hass = hass;
  return card;
}

describe('toggle button rendering', () => {
  it('shows "enabled" with status-on class when scheduler is enabled', () => {
    const card = mountCard(makeHass('enabled'));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    expect(btn.textContent.trim()).toBe('enabled');
    expect(btn.classList.contains('status-on')).toBe(true);
    expect(btn.classList.contains('status-off')).toBe(false);
  });

  it('shows "disabled" with status-off class when scheduler is disabled', () => {
    const card = mountCard(makeHass('disabled'));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    expect(btn.textContent.trim()).toBe('disabled');
    expect(btn.classList.contains('status-off')).toBe(true);
    expect(btn.classList.contains('status-on')).toBe(false);
  });
});

describe('toggle button click', () => {
  it('sends enable=0 when the scheduler is currently enabled', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass('enabled', send));
    card.shadowRoot.querySelector('.toggle-btn').click();
    expect(send).toHaveBeenCalledWith({
      type: 'foxess/set_scheduler_flag',
      deviceSN: DEVICE_SN,
      enable: 0,
    });
  });

  it('sends enable=1 when the scheduler is currently disabled', () => {
    const send = vi.fn().mockResolvedValue({ ok: true });
    const card = mountCard(makeHass('disabled', send));
    card.shadowRoot.querySelector('.toggle-btn').click();
    expect(send).toHaveBeenCalledWith({
      type: 'foxess/set_scheduler_flag',
      deviceSN: DEVICE_SN,
      enable: 1,
    });
  });

  it('disables the button while the request is in flight', () => {
    const card = mountCard(makeHass('enabled', vi.fn().mockReturnValue(new Promise(() => {}))));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    btn.click();
    expect(btn.disabled).toBe(true);
  });

  it('re-enables the button when the request fails', async () => {
    const send = vi.fn().mockRejectedValue(new Error('Network error'));
    const card = mountCard(makeHass('enabled', send));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    btn.click();
    await new Promise(resolve => setTimeout(resolve, 0));
    expect(btn.disabled).toBe(false);
  });
});
